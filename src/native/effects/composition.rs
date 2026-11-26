//! Explicit argument/result routes for calls made by trusted native bodies.
use super::*;
use crate::{
    analysis::effects::{CursorAlias, ParameterEffects, Projection, ReturnOrigins, SummarySource},
    ir::hir::Type,
};

#[derive(Clone)]
pub(crate) struct Specification {
    arguments: Vec<Argument<String>>,
    result: Destination<String>,
}

#[derive(Clone, PartialEq, Eq)]
enum Argument<P> {
    Parameter(usize, Vec<P>),
    Temporary(String),
}

#[derive(Clone, PartialEq, Eq)]
enum Destination<P> {
    Discard,
    Return(Vec<P>),
    Store {
        parameter: usize,
        path: Vec<P>,
    },
    Temporary {
        name: String,
        returned: Option<Vec<P>>,
    },
    Feedback {
        name: String,
        returns: bool,
    },
    Cache {
        name: String,
        parameter: usize,
        path: Vec<P>,
    },
}

fn underlying(mut ty: &str) -> &str {
    while let Some(inner) = ty
        .strip_prefix("__RuskReadonly<")
        .and_then(|ty| ty.strip_suffix('>'))
    {
        ty = inner;
    }
    ty
}

fn temporary(text: &str) -> Option<&str> {
    text.strip_prefix('$').filter(|name| {
        !name.is_empty() && name.bytes().all(|c| c.is_ascii_alphabetic() || c == b'_')
    })
}

impl Specification {
    /// `via (0.source,1) into return.cached`, `into 0.cached`, or `into discard`.
    /// A result routed `into $name` can be passed to a later call.
    /// `into $name to 0.cached` also allows the receiver to save that result.
    /// `into $name and return.Some.0` additionally shares it in the result.
    /// `into $name again` feeds a new result back to a previously bound local.
    /// `into $name again and return` also returns that local after the loop.
    pub(crate) fn parse(text: &str) -> Result<Self, String> {
        let (arguments, result) = text
            .split_once(" into ")
            .ok_or("native call mapping requires into")?;
        let arguments = arguments
            .strip_prefix('(')
            .and_then(|s| s.strip_suffix(')'))
            .ok_or("native call mapping requires an argument list")?;
        let arguments = if arguments.is_empty() {
            vec![]
        } else {
            arguments
                .split(',')
                .take(65)
                .map(|a| {
                    let a = a.trim();
                    if let Some(name) = temporary(a) {
                        return Ok(Argument::Temporary(name.into()));
                    }
                    let parsed = aliases::parse(&format!("return={a}"), usize::MAX)?;
                    let (_, parameter, path) = parsed.into_iter().next().unwrap();
                    Ok(Argument::Parameter(parameter, path))
                })
                .collect::<Result<Vec<_>, String>>()?
        };
        if arguments.len() > 64 {
            return Err("native call mapping argument limit exceeded".into());
        }
        let result = if result == "discard" {
            Destination::Discard
        } else if let Some((name, target)) = result.split_once(" to ") {
            let name = temporary(name).ok_or("native cursor cache requires a temporary")?;
            let (_, parameter, path) =
                aliases::parse(&format!("return={target}"), usize::MAX)?.remove(0);
            if path.is_empty() {
                return Err("native cursor cache requires a member destination".into());
            }
            Destination::Cache {
                name: name.into(),
                parameter,
                path,
            }
        } else if let Some(name) = result
            .strip_suffix(" again")
            .or_else(|| result.strip_suffix(" again and return"))
        {
            Destination::Feedback {
                name: temporary(name)
                    .ok_or("native loop feedback requires a temporary")?
                    .into(),
                returns: result.ends_with(" and return"),
            }
        } else if let Some((name, target)) = result.split_once(" and return.") {
            let name = temporary(name).ok_or("native result mapping requires a temporary")?;
            let path = aliases::parse(&format!("return.{target}=0"), 1)?
                .remove(0)
                .0;
            Destination::Temporary {
                name: name.into(),
                returned: Some(path),
            }
        } else if let Some(name) = temporary(result) {
            Destination::Temporary {
                name: name.into(),
                returned: None,
            }
        } else if result == "return" || result.starts_with("return.") {
            Destination::Return(aliases::parse(&format!("{result}=0"), 1)?.remove(0).0)
        } else {
            let (_, parameter, path) =
                aliases::parse(&format!("return={result}"), usize::MAX)?.remove(0);
            Destination::Store { parameter, path }
        };
        Ok(Self { arguments, result })
    }

    pub(crate) fn validate_bounds(&self, count: usize) -> Result<(), String> {
        if self
            .arguments
            .iter()
            .any(|arg| matches!(arg, Argument::Parameter(p, _) if *p >= count))
        {
            return Err("native call mapping argument out of range".into());
        }
        if let Destination::Store { parameter, .. } | Destination::Cache { parameter, .. } =
            self.result
            && parameter >= count
        {
            return Err("native call mapping destination out of range".into());
        }
        Ok(())
    }

    pub(crate) fn validate_arity(&self, count: usize) -> Result<(), String> {
        if self.arguments.len() != count {
            return Err("native call mapping arity mismatch".into());
        }
        Ok(())
    }

    pub(crate) fn resolve(
        &self,
        function: usize,
        outer_parameters: &[String],
        outer_result: &str,
        parameters: &[String],
        result: &str,
        types: &BTreeMap<String, Type>,
    ) -> Result<Dependency, String> {
        self.validate_bounds(outer_parameters.len())?;
        self.validate_arity(parameters.len())?;
        let arguments = self
            .arguments
            .iter()
            .zip(parameters)
            .map(|(arg, expected)| match arg {
                Argument::Temporary(name) => Ok(Argument::Temporary(name.clone())),
                Argument::Parameter(parameter, path) => {
                    let root = &outer_parameters[*parameter];
                    let path = aliases::resolve(root, path, types)?;
                    if crate::analysis::effects::project_type(root, &path, types)? != *expected {
                        return Err("native call mapping argument type mismatch".into());
                    }
                    Ok(Argument::Parameter(*parameter, path))
                }
            })
            .collect::<Result<Vec<_>, String>>()?;
        let project = |root: &str, path: &[String]| -> Result<Vec<Projection>, String> {
            let path = aliases::resolve(root, path, types)?;
            if crate::analysis::effects::project_type(root, &path, types)? != result {
                return Err("native call mapping result type mismatch".into());
            }
            Ok(path)
        };
        let result_path = match &self.result {
            Destination::Discard => Destination::Discard,
            Destination::Temporary { name, returned } => Destination::Temporary {
                name: name.clone(),
                returned: returned
                    .as_ref()
                    .map(|path| project(outer_result, path))
                    .transpose()?,
            },
            Destination::Return(path) => Destination::Return(project(outer_result, path)?),
            Destination::Feedback { name, returns } => {
                if *returns && outer_result != result {
                    return Err("native call mapping result type mismatch".into());
                }
                Destination::Feedback {
                    name: name.clone(),
                    returns: *returns && result != "Unit",
                }
            }
            Destination::Cache {
                name,
                parameter,
                path,
            } => Destination::Cache {
                name: name.clone(),
                parameter: *parameter,
                path: project(&outer_parameters[*parameter], path)?,
            },
            Destination::Store { parameter, path } => Destination::Store {
                parameter: *parameter,
                path: project(&outer_parameters[*parameter], path)?,
            },
        };
        Ok(Dependency {
            function,
            arguments,
            argument_types: parameters.to_vec(),
            quiet_result: !matches!(
                result_path,
                Destination::Temporary { .. }
                    | Destination::Feedback { .. }
                    | Destination::Cache { .. }
            ) || super::quiet_release(result, types),
            result: result_path,
            result_type: result.to_owned(),
        })
    }
}

#[derive(Clone, PartialEq, Eq)]
pub(crate) struct Dependency {
    pub function: usize,
    arguments: Vec<Argument<Projection>>,
    argument_types: Vec<String>,
    result: Destination<Projection>,
    result_type: String,
    quiet_result: bool,
}
impl Dependency {
    pub(crate) fn with_environment_arguments(
        &self,
        arguments: impl IntoIterator<Item = usize>,
    ) -> Self {
        let mut result = self.clone();
        result.arguments.extend(
            arguments
                .into_iter()
                .map(|parameter| Argument::Parameter(parameter, vec![])),
        );
        result
    }
}

/// Only resolved child effects can discharge a native dependency. Unknown
/// externs and native call cycles remain opaque during the fixed point;
/// returned provenance can conservatively widen without losing known effects.
pub(crate) fn compose(
    base: &Summary,
    dependencies: &[Dependency],
    summaries: &[Summary],
) -> Option<Summary> {
    let mut feedback = BTreeMap::new();
    // Native code describes a loop by assigning a call result back to a routed
    // local. Close the may-set before publishing any effects of the loop.
    for _ in 0..=64 {
        let (summary, next) = compose_pass(base, dependencies, summaries, &feedback)?;
        if next == feedback {
            return Some(summary);
        }
        feedback = next;
    }
    None
}

type Feedback<'a> = BTreeMap<&'a str, ReturnOrigins>;

fn compose_pass<'a>(
    base: &Summary,
    dependencies: &'a [Dependency],
    summaries: &[Summary],
    feedback: &Feedback<'a>,
) -> Option<(Summary, Feedback<'a>)> {
    let mut result = base.clone();
    let mut next_feedback = BTreeMap::new();
    let mut temporaries = BTreeMap::<&str, (&str, ReturnOrigins)>::new();
    for dependency in dependencies {
        let child = &summaries[dependency.function];
        if !matches!(
            child.source,
            SummarySource::Inferred | SummarySource::NativeContract
        ) || [
            child.io,
            child.external_write,
            child.may_fail,
            child.may_diverge,
        ]
        .contains(&Effect::Unknown)
            || child.parameters.iter().any(|p| {
                [p.read, p.write, p.structural, p.escape, p.retained].contains(&Effect::Unknown)
            })
        {
            return None;
        }
        result.io = result.io.max(child.io);
        result.external_write = result.external_write.max(child.external_write);
        result.may_fail = result.may_fail.max(child.may_fail);
        result.may_diverge = result.may_diverge.max(child.may_diverge);
        if base.cursor_step
            && (child.external_write != Effect::No
                || matches!(dependency.result, Destination::Store { .. })
                || child.parameters.iter().any(|p| p.retained != Effect::No))
        {
            return None;
        }
        let mut inputs = Vec::with_capacity(dependency.arguments.len());
        for (index, (arg, effect)) in dependency
            .arguments
            .iter()
            .zip(&child.parameters)
            .enumerate()
        {
            let (parameter, path) = match arg {
                Argument::Parameter(parameter, path) => (parameter, path),
                Argument::Temporary(name) => {
                    let (ty, origin) = temporaries.get(name.as_str())?;
                    // An ordinary callback may change a private accumulator.
                    // Only a cursor step can write through a routed input
                    // alias and leave the remaining input routes stable.
                    if Some(underlying(ty))
                        != dependency
                            .argument_types
                            .get(index)
                            .map(|ty| underlying(ty))
                        || !base.cursor_step
                        || effect.retained != Effect::No
                        || origin.unknown
                        || (!child.cursor_step
                            && (effect.write != Effect::No || effect.structural != Effect::No)
                            && !origin.aliases.is_empty())
                    {
                        return None;
                    }
                    result.affect(
                        origin,
                        &ParameterEffects {
                            escape: Effect::No,
                            ..effect.clone()
                        },
                    );
                    inputs.push(origin.clone());
                    continue;
                }
            };
            if base.cursor_step
                && !child.cursor_step
                && (effect.write != Effect::No || effect.structural != Effect::No)
            {
                return None;
            }
            inputs.push(ReturnOrigins {
                aliases: [ReturnAlias {
                    result_path: vec![],
                    parameter: *parameter,
                    parameter_path: path.clone(),
                }]
                .into(),
                ..Default::default()
            });
            let parent = &mut result.parameters[*parameter];
            // Parameter effects are currently whole-argument may sets. A
            // projected write/retention must conservatively affect its root.
            let mut passed = ParameterEffects {
                escape: effect.retained,
                ..effect.clone()
            };
            if base.cursor_step {
                if passed.write != Effect::No || passed.structural != Effect::No {
                    let mut paths = passed.paths()?;
                    paths = paths
                        .into_iter()
                        .map(|mut write| {
                            write.path.splice(..0, path.iter().cloned());
                            write
                        })
                        .collect();
                    if paths.iter().any(|write| write.path.len() > 16) {
                        return None;
                    }
                    passed.root_only &= path.is_empty();
                    passed.write_paths = Some(paths);
                }
                parent.join(&passed);
                continue;
            }
            parent.read = parent.read.max(passed.read);
            if passed.write != Effect::No || passed.structural != Effect::No {
                parent.root_only = false;
                parent.write_paths = None;
            }
            parent.write = parent.write.max(passed.write);
            parent.structural = parent.structural.max(passed.structural);
            parent.escape = parent.escape.max(passed.escape);
            if passed.retained != Effect::No {
                parent.readonly_sealed = false;
                parent.readonly_sealed_paths.clear();
            }
            parent.retained = parent.retained.max(passed.retained);
        }
        for cache in &child.cursor_aliases {
            if !base.cursor_step {
                return None;
            }
            let input = &inputs[cache.parameter];
            let mut source = input.clone();
            for projection in &cache.source_path {
                source = source.project(projection.clone());
            }
            if source.unknown {
                return None;
            }
            for owner in &input.aliases {
                let Some(tail) = cache
                    .target_path
                    .strip_prefix(owner.result_path.as_slice())
                    .filter(|tail| !tail.is_empty())
                else {
                    // Replacing a reference inside a private object does not
                    // change the referenced object that used to be there.
                    continue;
                };
                for alias in &source.aliases {
                    if alias.parameter != owner.parameter {
                        return None;
                    }
                    result.cursor_aliases.insert(CursorAlias {
                        parameter: owner.parameter,
                        target_path: owner
                            .parameter_path
                            .iter()
                            .chain(tail)
                            .chain(&alias.result_path)
                            .cloned()
                            .collect(),
                        source_path: alias.parameter_path.clone(),
                    });
                }
            }
        }
        if let Destination::Temporary { name, .. } | Destination::Cache { name, .. } =
            &dependency.result
        {
            if !base.cursor_step
                || child.returned.unknown
                || temporaries.contains_key(name.as_str())
            {
                return None;
            }
            let origin = child.returned.substitute(&inputs, Default::default());
            // A fresh value can be destroyed between calls. Foreign types may
            // execute arbitrary code when the last shared handle is released.
            if origin.fresh && !dependency.quiet_result {
                return None;
            }
            if let Destination::Cache {
                parameter, path, ..
            } = &dependency.result
            {
                for alias in &origin.aliases {
                    // Caching in the cursor must never add references to another
                    // incoming object that the cursor did not already reach.
                    if alias.parameter != *parameter {
                        return None;
                    }
                    result.cursor_aliases.insert(CursorAlias {
                        parameter: *parameter,
                        target_path: path.iter().chain(&alias.result_path).cloned().collect(),
                        source_path: alias.parameter_path.clone(),
                    });
                }
            }
            let mut origin = origin;
            if let Some(prior) = feedback.get(name.as_str()) {
                origin.join(prior);
                if origin.unknown {
                    return None;
                }
            }
            temporaries.insert(name.as_str(), (&dependency.result_type, origin));
        }
        if let Destination::Feedback { name, returns } = &dependency.result {
            let (ty, current) = temporaries.get_mut(name.as_str())?;
            if !base.cursor_step || child.returned.unknown || *ty != dependency.result_type {
                return None;
            }
            let produced = child.returned.substitute(&inputs, Default::default());
            if produced.unknown || (produced.fresh && !dependency.quiet_result) {
                return None;
            }
            current.join(&produced);
            if current.unknown {
                return None;
            }
            next_feedback.insert(name.as_str(), current.clone());
            if *returns {
                result.returned = current.clone();
                for alias in &result.returned.aliases {
                    let effect = &mut result.parameters[alias.parameter];
                    effect.escape = effect.escape.max(Effect::May);
                }
            }
        }
        let return_path = match &dependency.result {
            Destination::Return(path) => Some(path),
            Destination::Temporary { returned, .. } => returned.as_ref(),
            _ => None,
        };
        if let Some(target) = return_path {
            let returned = child.returned.substitute(&inputs, Default::default());
            if returned.unknown {
                result.returned.unknown = true;
                for parameter in &mut result.parameters {
                    parameter.escape = parameter.escape.max(Effect::May);
                }
            }
            for mut alias in returned.aliases {
                alias.result_path.splice(..0, target.iter().cloned());
                if alias.parameter_path.len() > 16 || alias.result_path.len() > 16 {
                    return None;
                }
                if alias.result_path.is_empty() && !returned.fresh {
                    result.returned.fresh = false;
                }
                result.parameters[alias.parameter].escape =
                    result.parameters[alias.parameter].escape.max(Effect::May);
                result.returned.aliases.insert(alias);
            }
        }
        if let Destination::Store { parameter, .. } = &dependency.result {
            // The body stores the returned object or its contents into an
            // existing argument. Root destinations denote content assignment,
            // never rebinding the caller's argument reference. Effects are
            // whole-argument may sets until a native heap model is available.
            let target = &mut result.parameters[*parameter];
            target.read = target.read.max(Effect::May);
            target.root_only = false;
            target.write_paths = None;
            target.write = target.write.max(Effect::May);
            target.structural = target.structural.max(Effect::May);
            if child.returned.unknown {
                for parameter in &mut result.parameters {
                    parameter.escape = parameter.escape.max(Effect::May);
                    parameter.readonly_sealed = false;
                    parameter.readonly_sealed_paths.clear();
                    parameter.retained = parameter.retained.max(Effect::May);
                }
            } else {
                for alias in &child.returned.aliases {
                    let Argument::Parameter(parameter, _) = dependency.arguments[alias.parameter]
                    else {
                        return None;
                    };
                    let effect = &mut result.parameters[parameter];
                    effect.escape = effect.escape.max(Effect::May);
                    effect.retained = effect.retained.max(Effect::May);
                }
            }
        }
        if result.returned.aliases.len() > 64
            || result.cursor_aliases.len() > 64
            || result
                .cursor_aliases
                .iter()
                .any(|alias| alias.target_path.len() > 16 || alias.source_path.len() > 16)
        {
            return None;
        }
    }
    // Native bodies have no CFG/heap model. A direct write or a child can
    // replace a routed member with another argument, after which later writes
    // and retention no longer necessarily affect the original route's root.
    // Widen across arguments as well as returned origins. Legacy dependencies
    // without routes retain their existing whole-operation contracts.
    if !base.cursor_step
        && !dependencies.is_empty()
        && (result.external_write != Effect::No
            || result
                .parameters
                .iter()
                .any(|p| p.write != Effect::No || p.structural != Effect::No))
    {
        let structural = if result.external_write != Effect::No {
            Effect::May
        } else {
            result
                .parameters
                .iter()
                .map(|p| p.structural)
                .max()
                .unwrap_or(Effect::No)
        };
        let retained = result
            .parameters
            .iter()
            .map(|p| p.retained)
            .max()
            .unwrap_or(Effect::No);
        for parameter in &mut result.parameters {
            parameter.root_only = false;
            parameter.write_paths = None;
            parameter.write = parameter.write.max(Effect::May);
            parameter.structural = parameter.structural.max(structural);
            if retained != Effect::No {
                parameter.readonly_sealed = false;
                parameter.readonly_sealed_paths.clear();
            }
            parameter.retained = parameter.retained.max(retained);
            parameter.escape = parameter.escape.max(Effect::May);
        }
        result.returned.unknown = true;
    }
    // A call that produces and returns the cache itself must describe both
    // the previously cached value and the value written during this call.
    let mut pending: Vec<_> = result.returned.aliases.iter().cloned().collect();
    while let Some(alias) = pending.pop() {
        for cache in &result.cursor_aliases {
            if alias.parameter != cache.parameter {
                continue;
            }
            let mut derived = alias.clone();
            if let Some(tail) = alias
                .parameter_path
                .strip_prefix(cache.target_path.as_slice())
            {
                derived.parameter_path = cache.source_path.iter().chain(tail).cloned().collect();
            } else if let Some(tail) = cache
                .target_path
                .strip_prefix(alias.parameter_path.as_slice())
            {
                derived.result_path.extend_from_slice(tail);
                derived.parameter_path.clone_from(&cache.source_path);
            } else {
                continue;
            }
            if derived.parameter_path.len() > 16 || derived.result_path.len() > 16 {
                return None;
            }
            if result.returned.aliases.insert(derived.clone()) {
                if result.returned.aliases.len() > 64 {
                    return None;
                }
                pending.push(derived);
            }
        }
    }
    if result.returned.unknown {
        result.returned = crate::analysis::effects::ReturnOrigins {
            unknown: true,
            ..Default::default()
        };
    }
    Some((result, next_feedback))
}

#[cfg(test)]
mod tests;
