//! Dependencies between explicitly declared target-language fragments.
use super::*;

#[derive(Clone)]
pub(super) struct Symbol {
    pub code: String,
    dependencies: BTreeSet<String>,
    optional: bool,
    opaque: bool,
    span: Span,
}

fn symbol_dependencies(name: &Name, text: Option<&str>) -> Result<BTreeSet<String>, String> {
    let mut dependencies = BTreeSet::new();
    if let Some(text) = text {
        for dependency in text.split(',').map(str::trim) {
            let mut chars = dependency.chars();
            if !chars
                .next()
                .is_some_and(|c| c.is_ascii_alphabetic() || c == '_')
                || !chars.all(|c| c.is_ascii_alphanumeric() || c == '_')
            {
                return Err(name.span.error("invalid native symbol dependency"));
            }
            if !dependencies.insert(dependency.to_string()) {
                return Err(name.span.error("duplicate native symbol dependency"));
            }
        }
    }
    Ok(dependencies)
}

impl Compiler {
    pub(super) fn register_symbol(
        &mut self,
        name: &Name,
        properties: &BTreeMap<String, String>,
        origin: Origin,
    ) -> Result<(), String> {
        validate(name, properties, &["code", "depends", "optional"])?;
        let optional = match properties.get("optional").map(String::as_str) {
            None => false,
            Some("true") if origin == Origin::StandardLibrary => true,
            Some(_) => {
                return Err(name
                    .span
                    .error("optional native symbols require the embedded standard library"));
            }
        };
        let dependencies =
            symbol_dependencies(name, properties.get("depends").map(String::as_str))?;
        let symbol = Symbol {
            code: property(name, properties, "code")?,
            dependencies,
            optional,
            opaque: origin == Origin::User,
            span: name.span.clone(),
        };
        if self.symbols.insert(name.text.clone(), symbol).is_some() {
            return Err(name.span.error("duplicate symbol"));
        }
        Ok(())
    }

    pub(super) fn register_native_resource_requirements(
        &mut self,
        name: &Name,
        properties: &BTreeMap<String, String>,
    ) -> Result<(), String> {
        if let Some(text) = properties.get("depends") {
            let dependencies = symbol_dependencies(name, Some(text))?;
            self.native_resource_requirements
                .insert(name.span.clone(), dependencies);
        }
        Ok(())
    }

    pub(super) fn validate_native_resource_requirements(&self) -> Result<(), String> {
        for (span, dependencies) in &self.native_resource_requirements {
            if let Some(name) = dependencies
                .iter()
                .find(|name| !self.symbols.contains_key(*name))
            {
                return Err(span.error(format!("unknown native symbol dependency '{name}'")));
            }
        }
        Ok(())
    }

    pub(super) fn has_opaque_symbols(&self) -> bool {
        self.symbols.values().any(|symbol| symbol.opaque)
    }

    pub(super) fn required_native_symbols<'a>(
        &'a self,
        declarations: impl Iterator<Item = (Origin, &'a Span)>,
    ) -> BTreeSet<&'a str> {
        // Ordinary user symbols may initialize state. Their bodies, like legacy
        // user externs, can reference any of the historically available runtime.
        if self.has_opaque_symbols() {
            return self.symbols.keys().map(String::as_str).collect();
        }
        let mut pending: Vec<_> = self
            .symbols
            .iter()
            .filter(|(_, symbol)| !symbol.optional)
            .map(|(name, _)| name.as_str())
            .collect();
        for (origin, span) in declarations {
            if let Some(dependencies) = self.native_resource_requirements.get(span) {
                pending.extend(dependencies.iter().map(String::as_str));
            } else if origin == Origin::User {
                return self.symbols.keys().map(String::as_str).collect();
            }
        }
        let mut required = BTreeSet::new();
        while let Some(name) = pending.pop() {
            if required.insert(name) {
                pending.extend(self.symbols[name].dependencies.iter().map(String::as_str));
            }
        }
        required
    }

    pub(super) fn prepare_symbols(&mut self) -> Result<(), String> {
        let mut incoming = BTreeMap::new();
        let mut dependents = BTreeMap::<String, BTreeSet<String>>::new();
        let mut ready = BTreeSet::new();
        let mut edges = 0;
        for (name, symbol) in &self.symbols {
            if self.symbols.len() > 4096 {
                return Err(symbol.span.error("native symbol limit exceeded"));
            }
            for dependency in &symbol.dependencies {
                if !self.symbols.contains_key(dependency) {
                    return Err(symbol
                        .span
                        .error(format!("unknown native symbol dependency '{dependency}'")));
                }
                edges += 1;
                if edges > 65536 {
                    return Err(symbol
                        .span
                        .error("native symbol dependency work limit exceeded"));
                }
                dependents
                    .entry(dependency.clone())
                    .or_default()
                    .insert(name.clone());
            }
            incoming.insert(name.clone(), symbol.dependencies.len());
            if symbol.dependencies.is_empty() {
                ready.insert(name.clone());
            }
        }
        self.symbol_order.clear();
        while let Some(name) = ready.pop_first() {
            if let Some(children) = dependents.get(&name) {
                for child in children {
                    let count = incoming.get_mut(child).unwrap();
                    *count -= 1;
                    if *count == 0 {
                        ready.insert(child.clone());
                    }
                }
            }
            self.symbol_order.push(name);
        }
        if self.symbol_order.len() != self.symbols.len() {
            let mut name = incoming.iter().find(|(_, n)| **n > 0).unwrap().0.clone();
            let mut path = vec![];
            let mut visited = BTreeMap::new();
            loop {
                if let Some(&start) = visited.get(&name) {
                    let mut cycle = path[start..].to_vec();
                    cycle.push(name.clone());
                    return Err(self.symbols[&name].span.error(format!(
                        "native symbol dependency cycle: {}",
                        cycle.join(" -> ")
                    )));
                }
                visited.insert(name.clone(), path.len());
                path.push(name.clone());
                name = self.symbols[&name]
                    .dependencies
                    .iter()
                    .find(|n| incoming[*n] > 0)
                    .unwrap()
                    .clone();
            }
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    fn add(compiler: &mut Compiler, name: &str, dependencies: Option<&str>) -> Result<(), String> {
        let name = Name {
            constant: None,
            text: name.into(),
            span: Span {
                file: "symbols.rusk".into(),
                line: 1,
                column: 1,
            },
        };
        let mut properties = BTreeMap::from([("code".into(), format!("// {name:?}"))]);
        if let Some(text) = dependencies {
            properties.insert("depends".into(), text.into());
        }
        compiler.register_symbol(&name, &properties, Origin::User)
    }
    #[test]
    fn native_symbols_order_forward_and_diamond_dependencies_once() {
        let mut compiler = Compiler::default();
        add(&mut compiler, "Alpha", Some("Beta,Zeta")).unwrap();
        add(&mut compiler, "Beta", Some("Zeta")).unwrap();
        add(&mut compiler, "Zeta", None).unwrap();
        compiler.prepare_symbols().unwrap();
        assert_eq!(compiler.symbol_order, ["Zeta", "Beta", "Alpha"]);
        assert!(
            add(&mut compiler, "Alpha", None)
                .unwrap_err()
                .contains("duplicate symbol")
        );
    }
    #[test]
    fn native_symbol_errors_validate_missing_cycles_and_dependency_syntax() {
        for dependency in ["", "a,a", "a b", "a;other", "a::other"] {
            assert!(
                add(&mut Compiler::default(), "Root", Some(dependency)).is_err(),
                "{dependency}"
            );
        }
        let mut compiler = Compiler::default();
        add(&mut compiler, "Root", Some("Missing")).unwrap();
        assert!(
            compiler
                .prepare_symbols()
                .unwrap_err()
                .contains("unknown native symbol dependency 'Missing'")
        );
        let mut compiler = Compiler::default();
        add(&mut compiler, "Alpha", Some("Beta")).unwrap();
        add(&mut compiler, "Beta", Some("Alpha")).unwrap();
        let error = compiler.prepare_symbols().unwrap_err();
        assert!(error.contains("Alpha -> Beta -> Alpha"), "{error}");
    }
    #[test]
    fn native_symbol_sorting_is_iterative_and_bounded() {
        let mut compiler = Compiler::default();
        add(&mut compiler, "s0", None).unwrap();
        for i in 1..4096 {
            add(
                &mut compiler,
                &format!("s{i}"),
                Some(&format!("s{}", i - 1)),
            )
            .unwrap();
        }
        compiler.prepare_symbols().unwrap();
        assert_eq!(compiler.symbol_order.len(), 4096);
        add(&mut compiler, "overflow", None).unwrap();
        assert!(
            compiler
                .prepare_symbols()
                .unwrap_err()
                .contains("native symbol limit")
        );
    }
}
