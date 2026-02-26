// Core type checking for AST nodes
//
// This module handles:
// - Trait implementation registration and coherence checking
// - Item registration (first pass)
// - Node type checking (second pass)
// - Pattern binding

impl TypeChecker {
    fn register_trait_impl(&mut self, impl_block: &ImplBlock) -> Result<(), TypeError> {
        let is_default = impl_block
            .attributes
            .iter()
            .any(|attr| attr.name == "default");

        let Some(trait_name) = &impl_block.trait_name else {
            if is_default {
                return Err(TypeError::Other(
                    "#[default] is only valid on trait impls".to_string(),
                ));
            }
            return Ok(());
        };

        let is_blanket = match &impl_block.target_type {
            AstType::Simple(name) => impl_block.generic_params.iter().any(|p| p == name),
            _ => false,
        };

        if is_default && !is_blanket {
            return Err(TypeError::Other(format!(
                "#[default] impl for trait `{}` must be a blanket impl (impl[T] Trait for T)",
                trait_name
            )));
        }

        let target_key = match &impl_block.target_type {
            AstType::Simple(name) => name.clone(),
            AstType::Generic { name, .. } => name.clone(),
            _ => "unknown".to_string(),
        };

        let registry = self
            .trait_impls
            .entry(trait_name.clone())
            .or_default();

        if is_blanket {
            if registry.blanket_impl {
                return Err(TypeError::Other(format!(
                    "duplicate blanket impl for trait `{}`",
                    trait_name
                )));
            }
            if !is_default && (!registry.specific_impls.is_empty() || registry.default_blanket_impl)
            {
                return Err(TypeError::Other(format!(
                    "overlapping impls for trait `{}`: blanket impl conflicts with existing impls",
                    trait_name
                )));
            }
            registry.blanket_impl = true;
            registry.default_blanket_impl = is_default;
            return Ok(());
        }

        if registry.specific_impls.contains(&target_key) {
            return Err(TypeError::Other(format!(
                "duplicate impl for trait `{}` and type `{}`",
                trait_name, target_key
            )));
        }

        if registry.blanket_impl && !registry.default_blanket_impl {
            return Err(TypeError::Other(format!(
                "overlapping impls for trait `{}`: specific impl for `{}` conflicts with blanket impl",
                trait_name, target_key
            )));
        }

        registry.specific_impls.insert(target_key);
        Ok(())
    }

    /// Helper to check match arms (pattern binding, guard, and body statements)
    fn check_match_arms(&mut self, arms: &[simple_parser::ast::MatchArm]) -> Result<(), TypeError> {
        for arm in arms {
            self.bind_pattern(&arm.pattern);
            if let Some(guard) = &arm.guard {
                let _ = self.infer_expr(guard)?;
            }
            self.check_block_with_macro_rules(&arm.body)?;
        }
        Ok(())
    }

    pub fn check_items(&mut self, items: &[Node]) -> Result<(), TypeError> {
        // Register built-in functions
        let range_ty = self.fresh_var();
        self.env.insert("range".to_string(), range_ty);
        let print_ty = self.fresh_var();
        self.env.insert("print".to_string(), print_ty);
        let len_ty = self.fresh_var();
        self.env.insert("len".to_string(), len_ty);
        let send_ty = self.fresh_var();
        self.env.insert("send".to_string(), send_ty);
        let recv_ty = self.fresh_var();
        self.env.insert("recv".to_string(), recv_ty);
        let reply_ty = self.fresh_var();
        self.env.insert("reply".to_string(), reply_ty);
        let join_ty = self.fresh_var();
        self.env.insert("join".to_string(), join_ty);
        let spawn_ty = self.fresh_var();
        self.env.insert("spawn".to_string(), spawn_ty);
        let spawn_isolated_ty = self.fresh_var();
        self.env.insert("spawn_isolated".to_string(), spawn_isolated_ty);
        // ThreadPool constructor
        let threadpool_ty = self.fresh_var();
        self.env.insert("ThreadPool".to_string(), threadpool_ty);
        // Option type constructors
        let some_ty = self.fresh_var();
        self.env.insert("Some".to_string(), some_ty);
        let none_ty = self.fresh_var();
        self.env.insert("None".to_string(), none_ty);
        // Result type constructors
        let ok_ty = self.fresh_var();
        self.env.insert("Ok".to_string(), ok_ty);
        let err_ty = self.fresh_var();
        self.env.insert("Err".to_string(), err_ty);

        // First pass: register all function, class, struct, const, static names
        for item in items {
            match item {
                Node::Function(func) => {
                    let ty = self.fresh_var();
                    self.env.insert(func.name.clone(), ty);
                }
                Node::Class(class) => {
                    let ty = self.fresh_var();
                    self.env.insert(class.name.clone(), ty);
                }
                Node::Struct(s) => {
                    let ty = self.fresh_var();
                    self.env.insert(s.name.clone(), ty);
                }
                Node::Enum(e) => {
                    let ty = self.fresh_var();
                    self.env.insert(e.name.clone(), ty);
                }
                Node::Trait(t) => {
                    // Register trait as a type for now
                    let ty = self.fresh_var();
                    self.env.insert(t.name.clone(), ty);
                }
                Node::Const(c) => {
                    let ty = self.fresh_var();
                    self.env.insert(c.name.clone(), ty);
                }
                Node::Static(s) => {
                    let ty = self.fresh_var();
                    self.env.insert(s.name.clone(), ty);
                }
                Node::Extern(ext) => {
                    let ty = self.fresh_var();
                    self.env.insert(ext.name.clone(), ty);
                }
                Node::ExternClass(ec) => {
                    // Register extern class as a type (FFI object type)
                    let ty = self.fresh_var();
                    self.env.insert(ec.name.clone(), ty);
                }
                Node::Macro(m) => {
                    // Register macro as a special type (macros are compile-time)
                    let ty = self.fresh_var();
                    self.env.insert(m.name.clone(), ty);
                    self.macros.insert(m.name.clone(), m.clone());
                }
                Node::Actor(a) => {
                    // Register actor as a type
                    let ty = self.fresh_var();
                    self.env.insert(a.name.clone(), ty);
                }
                Node::Mixin(mixin) => {
                    // Register mixin as a type (Feature #2200)
                    let ty = self.fresh_var();
                    self.env.insert(mixin.name.clone(), ty);
                }
                Node::TypeAlias(t) => {
                    // Register type alias
                    let ty = self.fresh_var();
                    self.env.insert(t.name.clone(), ty);
                }
                Node::Unit(u) => {
                    // Register unit type
                    let ty = self.fresh_var();
                    self.env.insert(u.name.clone(), ty);
                }
                Node::UnitFamily(uf) => {
                    // Register unit family type
                    let ty = self.fresh_var();
                    self.env.insert(uf.name.clone(), ty);
                }
                Node::CompoundUnit(cu) => {
                    // Register compound unit type
                    let ty = self.fresh_var();
                    self.env.insert(cu.name.clone(), ty);
                }
                Node::HandlePool(hp) => {
                    // Register handle pool for type (no new type introduced)
                    // The pool manages handles to the type specified in type_name
                    let ty = self.fresh_var();
                    self.env.insert(format!("__handle_pool_{}", hp.type_name), ty);
                }
                Node::Bitfield(bf) => {
                    // Register bitfield as a type
                    let ty = self.fresh_var();
                    self.env.insert(bf.name.clone(), ty);
                }
                Node::Impl(_) => {
                    // Impl blocks don't introduce new names
                }
                Node::Let(_)
                | Node::Assignment(_)
                | Node::Return(_)
                | Node::If(_)
                | Node::Match(_)
                | Node::For(_)
                | Node::While(_)
                | Node::Loop(_)
                | Node::Break(_)
                | Node::Continue(_)
                | Node::Assert(_)
                | Node::Assume(_)
                | Node::Admit(_)
                | Node::ProofHint(_)
                | Node::Calc(_)
                | Node::Context(_)
                | Node::With(_)
                | Node::Expression(_)
                | Node::Pass(_)
                | Node::Skip(_)
                | Node::Guard(_)
                | Node::Defer(_)
                | Node::ClassAlias(_)
                | Node::FunctionAlias(_) => {
                    // Statement nodes at module level are checked in second pass
                }
                // Module system nodes (parsed but not type-checked at this level)
                Node::ModDecl(_)
                | Node::UseStmt(_)
                | Node::MultiUse(_)
                | Node::CommonUseStmt(_)
                | Node::ExportUseStmt(_)
                | Node::StructuredExportStmt(_)
                | Node::AutoImportStmt(_)
                | Node::RequiresCapabilities(_)
                | Node::LeanBlock(_) => {
                    // Module system nodes and embedded lean blocks don't introduce type bindings directly
                }
                // AOP nodes (declarative configuration, not type bindings)
                Node::AopAdvice(_)
                | Node::DiBinding(_)
                | Node::ArchitectureRule(_)
                | Node::MockDecl(_) => {
                    // AOP nodes are declarative and don't introduce type bindings
                }
                Node::InterfaceBinding(binding) => {
                    // Register interface binding for static polymorphism
                    // bind Logger = ConsoleLogger means Logger -> ConsoleLogger (static dispatch)
                    let impl_type = self.ast_type_to_type(&binding.impl_type);
                    self.interface_bindings.insert(binding.interface_name.clone(), impl_type);
                }
                Node::LiteralFunction(_) => {
                    // Literal functions don't introduce new type bindings
                    // They register suffix → type mappings at runtime
                }
                Node::InlineAsm(_) => {
                    // Inline assembly doesn't introduce type bindings
                }
                Node::Newtype(nt) => {
                    // Register newtype wrapper as a type
                    let ty = self.fresh_var();
                    self.env.insert(nt.name.clone(), ty);
                }
                Node::Extend(_) => {
                    // Extension methods don't introduce new type names
                }
            }
        }
        // Second pass: check all nodes in order, enforcing macro definition order
        for item in items {
            if let Node::Macro(m) = item {
                self.available_macros.insert(m.name.clone());
            }
            self.check_node(item)?;
        }
        Ok(())
    }

    fn check_node(&mut self, node: &Node) -> Result<(), TypeError> {
        match node {
            Node::Let(let_stmt) => {
                if let Some(expr) = &let_stmt.value {
                    let inferred_ty = self.infer_expr(expr)?;

                    // Extract type annotation from Pattern::Typed or let_stmt.ty
                    let type_annotation = match &let_stmt.pattern {
                        Pattern::Typed { ty, .. } => Some(ty),
                        _ => let_stmt.ty.as_ref(),
                    };

                    // If there's a type annotation, check for ConstKeySet validation
                    if let Some(ref ast_ty) = type_annotation {
                        let expected_ty = self.ast_type_to_type(ast_ty);
                        // Validate dict keys against ConstKeySet if applicable
                        self.validate_dict_const_keys(expr, &expected_ty)?;
                        // Check dyn Trait coercion: if target is dyn Trait, verify source implements trait
                        if let Type::DynTrait(ref trait_name) = expected_ty {
                            let source_type_name = match &inferred_ty {
                                Type::Named(name) => Some(name.clone()),
                                _ => None,
                            };
                            if let Some(ref src_name) = source_type_name {
                                let implements = self.trait_impls
                                    .get(trait_name)
                                    .map_or(false, |r| r.specific_impls.contains(src_name) || r.blanket_impl);
                                if !implements {
                                    return Err(TypeError::Other(format!(
                                        "type `{}` does not implement trait `{}` (required for dyn coercion)",
                                        src_name, trait_name
                                    )));
                                }
                            }
                        }
                        // Unify inferred type with expected type
                        let _ = self.unify(&inferred_ty, &expected_ty);
                    }

                    // Bind all identifiers in the pattern
                    self.bind_pattern(&let_stmt.pattern);
                }
                Ok(())
            }
            Node::Const(const_stmt) => {
                let ty = self.infer_expr(&const_stmt.value)?;
                self.env.insert(const_stmt.name.clone(), ty);
                Ok(())
            }
            Node::Static(static_stmt) => {
                let ty = self.infer_expr(&static_stmt.value)?;
                self.env.insert(static_stmt.name.clone(), ty);
                Ok(())
            }
            Node::Assignment(assign) => {
                let ty = self.infer_expr(&assign.value)?;
                // Python-like: assignment can create new variables
                if let Expr::Identifier(name) = &assign.target {
                    self.env.insert(name.clone(), ty);
                }
                Ok(())
            }
            Node::Function(func) => {
                // Register the function name in current scope (for nested functions)
                let func_ty = self.fresh_var();
                self.env.insert(func.name.clone(), func_ty.clone());

                let old_env = self.env.clone();
                for param in &func.params {
                    // Use type annotation if present, otherwise create fresh var
                    let ty = if let Some(ref ast_ty) = param.ty {
                        self.ast_type_to_type(ast_ty)
                    } else {
                        self.fresh_var()
                    };
                    self.env.insert(param.name.clone(), ty);
                }
                self.check_block_with_macro_rules(&func.body)?;
                self.env = old_env;
                // Re-add function name after restoring env (it was added before saving old_env)
                self.env.insert(func.name.clone(), func_ty);
                Ok(())
            }
            Node::Return(ret) => {
                if let Some(expr) = &ret.value {
                    let _ = self.infer_expr(expr)?;
                }
                Ok(())
            }
            Node::Expression(expr) => {
                let _ = self.infer_expr(expr)?;
                Ok(())
            }
            Node::If(if_stmt) => {
                let _ = self.infer_expr(&if_stmt.condition)?;
                // Handle if let pattern binding
                if let Some(pattern) = &if_stmt.let_pattern {
                    self.bind_pattern(pattern);
                }
                self.check_block_with_macro_rules(&if_stmt.then_block)?;
                for (elif_pattern, cond, block) in &if_stmt.elif_branches {
                    let _ = self.infer_expr(cond)?;
                    if let Some(pattern) = elif_pattern {
                        self.bind_pattern(pattern);
                    }
                    self.check_block_with_macro_rules(block)?;
                }
                if let Some(block) = &if_stmt.else_block {
                    self.check_block_with_macro_rules(block)?;
                }
                Ok(())
            }
            Node::While(while_stmt) => {
                let _ = self.infer_expr(&while_stmt.condition)?;
                // Handle while let pattern binding
                if let Some(pattern) = &while_stmt.let_pattern {
                    self.bind_pattern(pattern);
                }
                self.check_block_with_macro_rules(&while_stmt.body)?;
                Ok(())
            }
            Node::For(for_stmt) => {
                let _ = self.infer_expr(&for_stmt.iterable)?;
                // Bind all identifiers in the pattern (handles tuple, array, struct, etc.)
                self.bind_pattern(&for_stmt.pattern);
                self.check_block_with_macro_rules(&for_stmt.body)?;
                Ok(())
            }
            Node::Loop(loop_stmt) => {
                self.check_block_with_macro_rules(&loop_stmt.body)?;
                Ok(())
            }
            Node::Context(ctx_stmt) => {
                // Check the context expression
                let _ = self.infer_expr(&ctx_stmt.context)?;
                // Check body statements - note: in context blocks, unknown methods
                // are dispatched to the context object, so we allow more flexibility
                for stmt in &ctx_stmt.body.statements {
                    // Be lenient with type checking inside context blocks
                    let _ = self.check_node(stmt);
                }
                Ok(())
            }
            Node::Match(match_stmt) => {
                let _ = self.infer_expr(&match_stmt.subject)?;
                self.check_match_arms(&match_stmt.arms)?;
                Ok(())
            }
            Node::Trait(trait_def) => {
                // Check all trait methods
                for method in &trait_def.methods {
                    let old_env = self.env.clone();
                    // Add self to environment for trait methods
                    let self_ty = self.fresh_var();
                    self.env.insert("self".to_string(), self_ty);
                    for param in &method.params {
                        if param.name != "self" {
                            let ty = self.fresh_var();
                            self.env.insert(param.name.clone(), ty);
                        }
                    }
                    self.check_block_with_macro_rules(&method.body)?;
                    self.env = old_env;
                }
                Ok(())
            }
            Node::Impl(impl_block) => {
                self.register_trait_impl(impl_block)?;
                // Check all impl methods
                for method in &impl_block.methods {
                    let old_env = self.env.clone();
                    // Add self to environment
                    let self_ty = self.fresh_var();
                    self.env.insert("self".to_string(), self_ty);
                    for param in &method.params {
                        if param.name != "self" {
                            let ty = self.fresh_var();
                            self.env.insert(param.name.clone(), ty);
                        }
                    }
                    self.check_block_with_macro_rules(&method.body)?;
                    self.env = old_env;
                }
                Ok(())
            }
            Node::Mixin(mixin) => {
                // Store mixin metadata for composition (Feature #2200)
                // Convert fields from AST to Type
                let fields: Vec<(String, Type)> = mixin
                    .fields
                    .iter()
                    .map(|f| (f.name.clone(), self.ast_type_to_type(&f.ty)))
                    .collect();

                // Convert methods to FunctionType
                let methods: Vec<(String, FunctionType)> = mixin
                    .methods
                    .iter()
                    .map(|m| {
                        let params: Vec<Type> = m
                            .params
                            .iter()
                            .filter_map(|p| p.ty.as_ref().map(|t| self.ast_type_to_type(t)))
                            .collect();
                        let ret = m
                            .return_type
                            .as_ref()
                            .map(|t| self.ast_type_to_type(t))
                            .unwrap_or(Type::Nil);
                        (m.name.clone(), FunctionType { params, ret })
                    })
                    .collect();

                // Store MixinInfo
                let required_mixins: Vec<String> = mixin.required_mixins.clone();

                let info = MixinInfo {
                    name: mixin.name.clone(),
                    type_params: mixin.generic_params.clone(),
                    fields,
                    methods,
                    required_traits: mixin.required_traits.clone(),
                    required_mixins,
                    required_methods: vec![],
                };
                self.mixins.insert(mixin.name.clone(), info);

                // Type check method bodies
                for method in &mixin.methods {
                    let old_env = self.env.clone();
                    // Add self to environment
                    let self_ty = self.fresh_var();
                    self.env.insert("self".to_string(), self_ty);
                    for param in &method.params {
                        if param.name != "self" {
                            let ty = self.fresh_var();
                            self.env.insert(param.name.clone(), ty);
                        }
                    }
                    self.check_block_with_macro_rules(&method.body)?;
                    self.env = old_env;
                }
                Ok(())
            }
            Node::With(with_stmt) => {
                // Check the resource expression
                let _ = self.infer_expr(&with_stmt.resource)?;
                // Bind the "as name" if present
                if let Some(name) = &with_stmt.name {
                    let ty = self.fresh_var();
                    self.env.insert(name.clone(), ty);
                }
                // Check body statements
                self.check_block_with_macro_rules(&with_stmt.body)?;
                Ok(())
            }
            _ => Ok(()),
        }
    }

    fn bind_pattern(&mut self, pattern: &Pattern) {
        match pattern {
            Pattern::Identifier(name) => {
                let ty = self.fresh_var();
                self.env.insert(name.clone(), ty);
            }
            Pattern::MutIdentifier(name) => {
                let ty = self.fresh_var();
                self.env.insert(name.clone(), ty);
            }
            Pattern::MoveIdentifier(name) => {
                // Move pattern - binds name with move semantics (ownership transfer)
                let ty = self.fresh_var();
                self.env.insert(name.clone(), ty);
            }
            Pattern::Tuple(patterns) | Pattern::Array(patterns) => {
                for p in patterns {
                    self.bind_pattern(p);
                }
            }
            Pattern::Struct { fields, .. } => {
                for (_, p) in fields {
                    self.bind_pattern(p);
                }
            }
            Pattern::Enum { payload, .. } => {
                if let Some(patterns) = payload {
                    for p in patterns {
                        self.bind_pattern(p);
                    }
                }
            }
            Pattern::Or(patterns) => {
                for p in patterns {
                    self.bind_pattern(p);
                }
            }
            Pattern::Typed { pattern, .. } => {
                self.bind_pattern(pattern);
            }
            Pattern::Wildcard | Pattern::Literal(_) | Pattern::Rest | Pattern::Range { .. } => {
                // These patterns don't bind any names
            }
        }
    }

    /// Extract const_keys from FString expression
    ///
    /// Returns const_keys for direct FString literals (from type_meta)
    pub fn get_fstring_keys_from_expr(&self, expr: &Expr) -> Option<Vec<String>> {
        match expr {
            // Case 1: Direct FString literal - extract keys from type_meta
            Expr::FString { type_meta, .. } => type_meta.const_keys().cloned(),
            _ => None,
        }
    }

    /// Register FString const_keys for a variable binding
    ///
    /// When a variable is bound to an FString with known keys, store them
    /// so DependentKeys types (e.g., `var_name.keys`) can be resolved.
    pub fn register_fstring_keys(&mut self, var_name: &str, expr: &Expr) {
        if let Some(keys) = self.get_fstring_keys_from_expr(expr) {
            self.fstring_keys.insert(var_name.to_string(), keys);
        }
    }

    /// Resolve DependentKeys to ConstKeySet if possible
    pub fn resolve_dependent_keys(&self, source: &str) -> Option<Vec<String>> {
        self.fstring_keys.get(source).cloned()
    }

    /// Validate dict literal keys against ConstKeySet type annotation
    ///
    /// If the expected type is Dict<ConstKeySet, V>, extract literal string keys
    /// from the dict expression and validate they match the expected keys.
    fn validate_dict_const_keys(&self, expr: &Expr, expected_ty: &Type) -> Result<(), TypeError> {
        // Check if expected type is Dict with ConstKeySet key type
        let expected_keys: Vec<String> = match expected_ty {
            Type::Dict { key, .. } => {
                if let Type::ConstKeySet { keys } = key.as_ref() {
                    keys.clone()
                } else {
                    return Ok(()); // Not a ConstKeySet, skip validation
                }
            }
            Type::Generic { name, args } if name == "Dict" && !args.is_empty() => {
                if let Type::ConstKeySet { keys } = &args[0] {
                    keys.clone()
                } else {
                    return Ok(());
                }
            }
            _ => return Ok(()), // Not a Dict type, skip validation
        };

        // Extract literal keys from dict expression
        let dict_entries = match expr {
            Expr::Dict(entries) => entries,
            _ => return Ok(()), // Not a dict literal, skip validation
        };

        let mut literal_keys: Vec<String> = Vec::new();
        let mut has_non_literal = false;

        for (key_expr, _) in dict_entries {
            match key_expr {
                // Plain string literal
                Expr::String(s) => literal_keys.push(s.clone()),
                // FString that is a pure literal (no interpolation)
                Expr::FString { parts, .. } if parts.len() == 1 => {
                    use simple_parser::ast::FStringPart;
                    if let FStringPart::Literal(s) = &parts[0] {
                        literal_keys.push(s.clone());
                    } else {
                        has_non_literal = true;
                    }
                }
                Expr::DictSpread(_) => {
                    // Spread expressions add unknown keys at runtime
                    has_non_literal = true;
                }
                _ => {
                    // Non-literal key expression
                    has_non_literal = true;
                }
            }
        }

        // If there are non-literal keys, we can't fully validate at compile time
        // but we can still check that literal keys are valid
        if has_non_literal && literal_keys.is_empty() {
            // All keys are runtime-determined, can't validate
            return Ok(());
        }

        // Validate literal keys against expected ConstKeySet
        let validation = crate::validate_dict_keys_against_const_set(
            &literal_keys.iter().map(|k| Some(k.clone())).collect::<Vec<_>>(),
            &expected_keys,
        );

        // Report errors for unknown keys
        if let Some(unknown) = validation.unknown_keys.first() {
            return Err(TypeError::ConstKeyNotFound {
                key: unknown.clone(),
                expected_keys: expected_keys.clone(),
            });
        }

        // If all keys are literal, check for missing required keys
        if !has_non_literal {
            if let Some(missing) = validation.missing_keys.first() {
                return Err(TypeError::ConstKeyMissing {
                    key: missing.clone(),
                    provided_keys: literal_keys.clone(),
                });
            }
        }

        Ok(())
    }
}
