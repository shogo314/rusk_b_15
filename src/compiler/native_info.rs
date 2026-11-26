//! Per-function native semantics, separate from whole-program output requests.
use super::*;
use crate::analysis::effects::{Effect, Summary};
use crate::native::{effects::composition::Dependency, lowering::Lowering};

#[derive(Clone, Default)]
pub(super) struct NativeFunctionInfo {
    pub(super) contract: Option<Summary>,
    // None means there was no dependency registration. Some(empty) still marks
    // a conditional contract whose mapped calls must be proven before use.
    pub(super) dependencies: Option<BTreeSet<usize>>,
    pub(super) mapped_dependencies: Vec<Dependency>,
    pub(super) lowering: Option<Lowering>,
    pub(super) enum_operation: Option<enum_operations::Operation>,
    pub(super) unit_object: bool,
}
impl Compiler {
    pub(super) fn native_requests_for(
        &mut self,
        function: Option<usize>,
    ) -> &mut crate::native::NativeRequests {
        if let Some(id) = function {
            self.native_function_requests.entry(id).or_default()
        } else {
            let ty = self
                .rendering_native_types
                .last()
                .expect("native request owner");
            self.native_type_requests.entry(ty.clone()).or_default()
        }
    }

    pub(super) fn request_native_effect(
        &mut self,
        owner: Option<usize>,
        target: usize,
        query: crate::analysis::effects::Query,
    ) {
        self.native_effect_queries.insert((target, query));
        self.native_requests_for(owner)
            .effects
            .insert((target, query));
    }

    pub(super) fn compose_native_environment_contract(
        &self,
        id: usize,
        summaries: &[Summary],
        recursive: bool,
    ) -> Option<Summary> {
        let mut base = self.native_environment_contract(id)?;
        if recursive {
            base.may_diverge = Effect::May;
        }
        let owner_keys = self.native_capture_keys(id);
        let direct = self.native_dependencies(id).cloned().unwrap_or_default();
        let mapped = self.native_mappings(id);
        let dependencies = if owner_keys.is_empty() {
            direct.clone()
        } else {
            self.native_capture_dependencies(id)
                .into_iter()
                .filter(|dep| direct.contains(dep) || !mapped.iter().any(|m| m.function == *dep))
                .collect()
        };
        for &dependency in &dependencies {
            let mut visible = summaries[dependency].clone();
            visible
                .parameters
                .truncate(self.functions[dependency].params.len());
            if !crate::native::effects::dependency_covered(&base, &visible) {
                return None;
            }
        }
        let environment_arguments = |dependency| {
            self.native_capture_keys(dependency)
                .iter()
                .map(|key| {
                    self.functions[id].params.len()
                        + owner_keys
                            .iter()
                            .position(|candidate| candidate == key)
                            .expect("native capture dependency was propagated")
                })
                .collect::<Vec<_>>()
        };
        let mappings = mapped
            .iter()
            .map(|mapping| {
                mapping.with_environment_arguments(environment_arguments(mapping.function))
            })
            .collect::<Vec<_>>();
        let mut result = crate::native::effects::composition::compose(&base, &mappings, summaries)?;
        for dependency in dependencies {
            for (index, parameter) in environment_arguments(dependency).into_iter().enumerate() {
                let child = &summaries[dependency].parameters
                    [self.functions[dependency].params.len() + index];
                let parent = &mut result.parameters[parameter];
                parent.read = parent.read.max(child.read);
                if child.write != Effect::No || child.structural != Effect::No {
                    parent.root_only = false;
                    parent.write_paths = None;
                }
                parent.write = parent.write.max(child.write);
                parent.structural = parent.structural.max(child.structural);
                parent.escape = parent.escape.max(child.escape);
                if child.retained != Effect::No {
                    parent.readonly_sealed = false;
                    parent.readonly_sealed_paths.clear();
                }
                parent.retained = parent.retained.max(child.retained);
            }
        }
        Some(result)
    }

    pub(super) fn native_environment_contract(&self, index: usize) -> Option<Summary> {
        let contract = self.native_contract(index)?;
        let captures = self.capture_parameters(index).len();
        if captures == 0 {
            return Some(contract.clone());
        }
        if contract.source == crate::analysis::effects::SummarySource::NativeContract {
            let mut contract = contract.clone();
            contract
                .parameters
                .extend(std::iter::repeat_n(Default::default(), captures));
            return Some(contract);
        }
        if contract.source != crate::analysis::effects::SummarySource::ExternContract {
            // Built-in contracts need composition with the captured operations;
            // until proven, do not apply a source-arity contract to the ABI.
            return None;
        }
        use crate::analysis::effects::Effect;
        let mut guarantees = contract
            .parameters
            .iter()
            .map(|p| {
                (
                    p.write == Effect::No && p.structural == Effect::No,
                    p.escape == Effect::No,
                )
            })
            .collect::<Vec<_>>();
        guarantees.extend(std::iter::repeat_n((false, false), captures));
        Some(Summary::external(&guarantees))
    }
    pub(super) fn native_info_mut(&mut self, index: usize) -> &mut NativeFunctionInfo {
        self.native_info.entry(index).or_default()
    }
    pub(super) fn native_contract(&self, index: usize) -> Option<&Summary> {
        self.native_info.get(&index)?.contract.as_ref()
    }
    pub(super) fn native_dependencies(&self, index: usize) -> Option<&BTreeSet<usize>> {
        self.native_info.get(&index)?.dependencies.as_ref()
    }
    pub(super) fn native_mappings(&self, index: usize) -> &[Dependency] {
        self.native_info
            .get(&index)
            .map_or(&[], |info| info.mapped_dependencies.as_slice())
    }
    pub(super) fn native_lowering(&self, index: usize) -> Option<&Lowering> {
        self.native_info.get(&index)?.lowering.as_ref()
    }
    pub(super) fn native_unit_object(&self, index: usize) -> bool {
        self.native_info
            .get(&index)
            .is_some_and(|info| info.unit_object)
    }
}
