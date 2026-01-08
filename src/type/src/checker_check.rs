#[derive(Debug, Clone, PartialEq)]
enum ConstValue {
    Int(i64),
    Float(f64),
    Bool(bool),
    Str(String),
}

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
                | Node::Context(_)
                | Node::With(_)
                | Node::Expression(_) => {
                    // Statement nodes at module level are checked in second pass
                }
                // Module system nodes (parsed but not type-checked at this level)
                Node::ModDecl(_)
                | Node::UseStmt(_)
                | Node::CommonUseStmt(_)
                | Node::ExportUseStmt(_)
                | Node::AutoImportStmt(_)
                | Node::RequiresCapabilities(_) => {
                    // Module system nodes don't introduce type bindings directly
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
                    let _ty = self.infer_expr(expr)?;
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
                for (cond, block) in &if_stmt.elif_branches {
                    let _ = self.infer_expr(cond)?;
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
                    for param in &method.params {
                        let ty = self.fresh_var();
                        self.env.insert(param.name.clone(), ty);
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
                let info = MixinInfo {
                    name: mixin.name.clone(),
                    type_params: mixin.generic_params.clone(),
                    fields,
                    methods,
                    required_traits: mixin.required_traits.clone(),
                    required_methods: vec![], // TODO: Phase 2 Step 6
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

    fn check_block_with_macro_rules(
        &mut self,
        block: &simple_parser::ast::Block,
    ) -> Result<(), TypeError> {
        let mut seen_non_macro = false;
        let mut seen_tail_macro = false;

        for stmt in &block.statements {
            if let Some((macro_name, anchors)) = self.macro_invocation_anchors(stmt) {
                if anchors.iter().any(|a| matches!(a, simple_parser::ast::MacroAnchor::Head))
                    && seen_non_macro
                {
                    return Err(TypeError::Other(format!(
                        "macro '{}' with callsite.block.head must appear before non-macro statements",
                        macro_name
                    )));
                }
                if seen_tail_macro {
                    return Err(TypeError::Other(format!(
                        "macro '{}' appears after callsite.block.tail macro",
                        macro_name
                    )));
                }
                if anchors.iter().any(|a| matches!(a, simple_parser::ast::MacroAnchor::Tail)) {
                    seen_tail_macro = true;
                }
            } else {
                if seen_tail_macro {
                    return Err(TypeError::Other(
                        "non-macro statement appears after callsite.block.tail macro".into(),
                    ));
                }
                seen_non_macro = true;
            }

            self.check_node(stmt)?;
        }

        Ok(())
    }

    fn macro_invocation_anchors(
        &self,
        node: &Node,
    ) -> Option<(String, Vec<simple_parser::ast::MacroAnchor>)> {
        let name = match node {
            Node::Expression(Expr::MacroInvocation { name, .. }) => name.as_str(),
            _ => return None,
        };
        let macro_def = self.macros.get(name)?;
        let mut anchors = Vec::new();
        for item in &macro_def.contract {
            if let simple_parser::ast::MacroContractItem::Inject(inject) = item {
                anchors.push(inject.spec.anchor.clone());
            }
        }
        if anchors.is_empty() {
            None
        } else {
            Some((name.to_string(), anchors))
        }
    }

    fn apply_macro_intros(
        &mut self,
        macro_def: &MacroDef,
        const_bindings: &std::collections::HashMap<String, String>,
    ) -> Result<(), TypeError> {
        for item in &macro_def.contract {
            if let simple_parser::ast::MacroContractItem::Intro(intro) = item {
                self.apply_macro_intro_spec(&intro.spec, const_bindings)?;
            }
        }
        Ok(())
    }

    fn apply_macro_intro_spec(
        &mut self,
        spec: &MacroIntroSpec,
        const_bindings: &std::collections::HashMap<String, String>,
    ) -> Result<(), TypeError> {
        match spec {
            MacroIntroSpec::Decl(decl) => self.apply_macro_intro_decl(decl, const_bindings)?,
            MacroIntroSpec::For { .. } => {
                self.apply_macro_intro_for(spec, const_bindings)?;
            }
            MacroIntroSpec::If {
                condition,
                then_body,
                else_body,
            } => {
                if let Some(value) = self.eval_const_bool(condition, const_bindings) {
                    let active_body = if value { then_body } else { else_body };
                    for child in active_body {
                        self.apply_macro_intro_spec(child, const_bindings)?;
                    }
                } else {
                    return Err(TypeError::Other(
                        "macro intro if condition is not const-evaluable".into(),
                    ));
                }
            }
        }
        Ok(())
    }

    fn apply_macro_intro_decl(
        &mut self,
        decl: &MacroIntroDecl,
        const_bindings: &std::collections::HashMap<String, String>,
    ) -> Result<(), TypeError> {
        match decl.target {
            MacroTarget::Enclosing(simple_parser::ast::EnclosingTarget::Module)
            | MacroTarget::CallsiteBlock(_) => {}
            _ => return Ok(()),
        }

        match &decl.stub {
            simple_parser::ast::MacroDeclStub::Fn(stub) => {
                let name = substitute_macro_template(&stub.name, const_bindings);
                if self.env.contains_key(&name) {
                    return Err(TypeError::Other(format!(
                        "macro intro '{}' conflicts with existing symbol",
                        name
                    )));
                }
                let params = stub
                    .params
                    .iter()
                    .map(|p| self.ast_type_to_type(&p.ty))
                    .collect::<Vec<_>>();
                let ret = stub
                    .ret
                    .as_ref()
                    .map(|ty| self.ast_type_to_type(ty))
                    .unwrap_or_else(|| self.fresh_var());
                self.env.insert(
                    name,
                    Type::Function {
                        params,
                        ret: Box::new(ret),
                    },
                );
            }
            simple_parser::ast::MacroDeclStub::Field(stub) => {
                let name = substitute_macro_template(&stub.name, const_bindings);
                if self.env.contains_key(&name) {
                    return Err(TypeError::Other(format!(
                        "macro intro '{}' conflicts with existing symbol",
                        name
                    )));
                }
                let ty = self.ast_type_to_type(&stub.ty);
                self.env.insert(name, ty);
            }
            simple_parser::ast::MacroDeclStub::Var(stub) => {
                let name = substitute_macro_template(&stub.name, const_bindings);
                if self.env.contains_key(&name) {
                    return Err(TypeError::Other(format!(
                        "macro intro '{}' conflicts with existing symbol",
                        name
                    )));
                }
                let ty = self.ast_type_to_type(&stub.ty);
                self.env.insert(name, ty);
            }
            simple_parser::ast::MacroDeclStub::Type(stub) => {
                let name = substitute_macro_template(&stub.name, const_bindings);
                if self.env.contains_key(&name) {
                    return Err(TypeError::Other(format!(
                        "macro intro '{}' conflicts with existing symbol",
                        name
                    )));
                }
                self.env.insert(name.clone(), Type::Named(name));
            }
        }
        Ok(())
    }

    fn apply_macro_intro_for(
        &mut self,
        spec: &MacroIntroSpec,
        const_bindings: &std::collections::HashMap<String, String>,
    ) -> Result<(), TypeError> {
        let (name, range, body) = match spec {
            MacroIntroSpec::For { name, range, body } => (name, range, body),
            _ => return Ok(()),
        };
        let values = self.eval_const_range(range, const_bindings).ok_or_else(|| {
            TypeError::Other("macro intro for-range is not const-evaluable".into())
        })?;
        for value in values {
            let mut loop_bindings = const_bindings.clone();
            loop_bindings.insert(name.clone(), value.to_string());
            for child in body {
                self.apply_macro_intro_spec(child, &loop_bindings)?;
            }
        }
        Ok(())
    }

    fn eval_const_range(
        &self,
        range: &MacroConstRange,
        const_bindings: &std::collections::HashMap<String, String>,
    ) -> Option<Vec<i64>> {
        let start = self.eval_const_int(&range.start, const_bindings)?;
        let end = self.eval_const_int(&range.end, const_bindings)?;
        let mut values = Vec::new();
        if range.inclusive {
            for value in start..=end {
                values.push(value);
            }
        } else {
            for value in start..end {
                values.push(value);
            }
        }
        Some(values)
    }

    fn eval_const_bool(
        &self,
        expr: &Expr,
        const_bindings: &std::collections::HashMap<String, String>,
    ) -> Option<bool> {
        match self.eval_const_expr(expr, const_bindings)? {
            ConstValue::Bool(value) => Some(value),
            _ => None,
        }
    }

    fn eval_const_int(
        &self,
        expr: &Expr,
        const_bindings: &std::collections::HashMap<String, String>,
    ) -> Option<i64> {
        match self.eval_const_expr(expr, const_bindings)? {
            ConstValue::Int(value) => Some(value),
            _ => None,
        }
    }

    fn eval_const_expr(
        &self,
        expr: &Expr,
        const_bindings: &std::collections::HashMap<String, String>,
    ) -> Option<ConstValue> {
        match expr {
            Expr::Integer(value) | Expr::TypedInteger(value, _) => Some(ConstValue::Int(*value)),
            Expr::Float(value) | Expr::TypedFloat(value, _) => Some(ConstValue::Float(*value)),
            Expr::Bool(value) => Some(ConstValue::Bool(*value)),
            Expr::String(value) | Expr::TypedString(value, _) => {
                Some(ConstValue::Str(value.clone()))
            }
            Expr::FString(parts) => {
                let mut out = String::new();
                for part in parts {
                    match part {
                        simple_parser::ast::FStringPart::Literal(text) => out.push_str(text),
                        simple_parser::ast::FStringPart::Expr(_) => return None,
                    }
                }
                Some(ConstValue::Str(out))
            }
            Expr::Symbol(value) => Some(ConstValue::Str(value.clone())),
            Expr::Identifier(name) => const_bindings
                .get(name)
                .and_then(|text| self.const_value_from_binding(text)),
            Expr::Unary { op, operand } => {
                let value = self.eval_const_expr(operand, const_bindings)?;
                match (op, value) {
                    (UnaryOp::Neg, ConstValue::Int(i)) => Some(ConstValue::Int(-i)),
                    (UnaryOp::Neg, ConstValue::Float(f)) => Some(ConstValue::Float(-f)),
                    (UnaryOp::Not, ConstValue::Bool(b)) => Some(ConstValue::Bool(!b)),
                    (UnaryOp::BitNot, ConstValue::Int(i)) => Some(ConstValue::Int(!i)),
                    _ => None,
                }
            }
            Expr::Binary { op, left, right } => {
                let left_value = self.eval_const_expr(left, const_bindings)?;
                let right_value = self.eval_const_expr(right, const_bindings)?;
                self.eval_const_binop(op, left_value, right_value)
            }
            _ => None,
        }
    }

    fn eval_const_binop(
        &self,
        op: &BinOp,
        left: ConstValue,
        right: ConstValue,
    ) -> Option<ConstValue> {
        match op {
            BinOp::Add => match (left, right) {
                (ConstValue::Int(a), ConstValue::Int(b)) => Some(ConstValue::Int(a + b)),
                (ConstValue::Float(a), ConstValue::Float(b)) => Some(ConstValue::Float(a + b)),
                (ConstValue::Int(a), ConstValue::Float(b)) => Some(ConstValue::Float(a as f64 + b)),
                (ConstValue::Float(a), ConstValue::Int(b)) => Some(ConstValue::Float(a + b as f64)),
                (ConstValue::Str(a), ConstValue::Str(b)) => Some(ConstValue::Str(a + &b)),
                _ => None,
            },
            BinOp::Sub => match (left, right) {
                (ConstValue::Int(a), ConstValue::Int(b)) => Some(ConstValue::Int(a - b)),
                (ConstValue::Float(a), ConstValue::Float(b)) => Some(ConstValue::Float(a - b)),
                (ConstValue::Int(a), ConstValue::Float(b)) => Some(ConstValue::Float(a as f64 - b)),
                (ConstValue::Float(a), ConstValue::Int(b)) => Some(ConstValue::Float(a - b as f64)),
                _ => None,
            },
            BinOp::Mul => match (left, right) {
                (ConstValue::Int(a), ConstValue::Int(b)) => Some(ConstValue::Int(a * b)),
                (ConstValue::Float(a), ConstValue::Float(b)) => Some(ConstValue::Float(a * b)),
                (ConstValue::Int(a), ConstValue::Float(b)) => Some(ConstValue::Float(a as f64 * b)),
                (ConstValue::Float(a), ConstValue::Int(b)) => Some(ConstValue::Float(a * b as f64)),
                _ => None,
            },
            BinOp::Div => match (left, right) {
                (ConstValue::Int(a), ConstValue::Int(b)) => Some(ConstValue::Int(a / b)),
                (ConstValue::Float(a), ConstValue::Float(b)) => Some(ConstValue::Float(a / b)),
                (ConstValue::Int(a), ConstValue::Float(b)) => Some(ConstValue::Float(a as f64 / b)),
                (ConstValue::Float(a), ConstValue::Int(b)) => Some(ConstValue::Float(a / b as f64)),
                _ => None,
            },
            BinOp::Mod => match (left, right) {
                (ConstValue::Int(a), ConstValue::Int(b)) => Some(ConstValue::Int(a % b)),
                _ => None,
            },
            BinOp::Eq => Some(ConstValue::Bool(left == right)),
            BinOp::NotEq => Some(ConstValue::Bool(left != right)),
            BinOp::Lt => self.eval_const_compare(left, right, |a, b| a < b),
            BinOp::LtEq => self.eval_const_compare(left, right, |a, b| a <= b),
            BinOp::Gt => self.eval_const_compare(left, right, |a, b| a > b),
            BinOp::GtEq => self.eval_const_compare(left, right, |a, b| a >= b),
            BinOp::And => match (left, right) {
                (ConstValue::Bool(a), ConstValue::Bool(b)) => Some(ConstValue::Bool(a && b)),
                _ => None,
            },
            BinOp::Or => match (left, right) {
                (ConstValue::Bool(a), ConstValue::Bool(b)) => Some(ConstValue::Bool(a || b)),
                _ => None,
            },
            _ => None,
        }
    }

    fn eval_const_compare(
        &self,
        left: ConstValue,
        right: ConstValue,
        cmp: impl Fn(f64, f64) -> bool,
    ) -> Option<ConstValue> {
        match (left, right) {
            (ConstValue::Int(a), ConstValue::Int(b)) => Some(ConstValue::Bool(cmp(a as f64, b as f64))),
            (ConstValue::Float(a), ConstValue::Float(b)) => Some(ConstValue::Bool(cmp(a, b))),
            (ConstValue::Int(a), ConstValue::Float(b)) => Some(ConstValue::Bool(cmp(a as f64, b))),
            (ConstValue::Float(a), ConstValue::Int(b)) => Some(ConstValue::Bool(cmp(a, b as f64))),
            _ => None,
        }
    }

    fn const_value_from_binding(&self, text: &str) -> Option<ConstValue> {
        if text == "true" {
            return Some(ConstValue::Bool(true));
        }
        if text == "false" {
            return Some(ConstValue::Bool(false));
        }
        if let Ok(value) = text.parse::<i64>() {
            return Some(ConstValue::Int(value));
        }
        if let Ok(value) = text.parse::<f64>() {
            return Some(ConstValue::Float(value));
        }
        Some(ConstValue::Str(text.to_string()))
    }

    fn const_value_to_string(&self, value: &ConstValue) -> Option<String> {
        match value {
            ConstValue::Int(value) => Some(value.to_string()),
            ConstValue::Float(value) => Some(value.to_string()),
            ConstValue::Bool(value) => Some(value.to_string()),
            ConstValue::Str(value) => Some(value.clone()),
        }
    }

    fn macro_return_type(&mut self, macro_def: &MacroDef) -> Type {
        for item in &macro_def.contract {
            if let simple_parser::ast::MacroContractItem::Returns(ret) = item {
                return self.ast_type_to_type(&ret.ty);
            }
        }
        self.fresh_var()
    }

    fn build_macro_const_bindings(
        &self,
        macro_def: &MacroDef,
        args: &[simple_parser::ast::MacroArg],
    ) -> std::collections::HashMap<String, String> {
        let mut bindings = std::collections::HashMap::new();
        for (idx, param) in macro_def.params.iter().enumerate() {
            if !param.is_const {
                continue;
            }
            let Some(simple_parser::ast::MacroArg::Expr(expr)) = args.get(idx) else {
                continue;
            };
            if let Some(value) = self.eval_const_expr(expr, &bindings) {
                if let Some(text) = self.const_value_to_string(&value) {
                    bindings.insert(param.name.clone(), text);
                    continue;
                }
            }
            if let Some(text) = self.const_expr_to_string(expr) {
                bindings.insert(param.name.clone(), text);
            }
        }
        bindings
    }

    fn const_expr_to_string(&self, expr: &Expr) -> Option<String> {
        match expr {
            Expr::String(value) => Some(value.clone()),
            Expr::TypedString(value, _) => Some(value.clone()),
            Expr::FString(parts) => {
                let mut out = String::new();
                for part in parts {
                    match part {
                        simple_parser::ast::FStringPart::Literal(s) => out.push_str(s),
                        simple_parser::ast::FStringPart::Expr(_) => return None,
                    }
                }
                Some(out)
            }
            Expr::Identifier(name) => Some(name.clone()),
            Expr::Integer(value) => Some(value.to_string()),
            Expr::Float(value) => Some(value.to_string()),
            Expr::Bool(value) => Some(value.to_string()),
            Expr::Nil => Some("nil".to_string()),
            Expr::Symbol(value) => Some(value.clone()),
            _ => None,
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

    /// Check for field name conflicts between mixin and class/struct (Feature #2201)
    pub fn check_mixin_field_conflicts(
        &self,
        mixin_fields: &[(String, Type)],
        target_fields: &[(String, Type)],
    ) -> Vec<String> {
        let mut conflicts = Vec::new();
        for (mixin_name, _mixin_ty) in mixin_fields {
            if target_fields.iter().any(|(target_name, _)| target_name == mixin_name) {
                conflicts.push(mixin_name.clone());
            }
        }
        conflicts
    }

    /// Combine fields from multiple mixins, checking for conflicts (Feature #2201)
    pub fn combine_mixin_fields(
        &self,
        mixins: &[MixinInfo],
    ) -> Result<Vec<(String, Type)>, TypeError> {
        let mut combined = Vec::new();
        let mut seen_names = std::collections::HashSet::new();

        for mixin in mixins {
            for (name, ty) in &mixin.fields {
                if !seen_names.insert(name.clone()) {
                    return Err(TypeError::Other(format!(
                        "Field '{}' defined in multiple mixins",
                        name
                    )));
                }
                combined.push((name.clone(), ty.clone()));
            }
        }
        Ok(combined)
    }

    /// Apply mixin to a class/struct, merging fields and methods (Feature #2201)
    pub fn apply_mixin_to_type(
        &self,
        mixin: &MixinInfo,
        target_name: &str,
        target_fields: &[(String, Type)],
    ) -> Result<Vec<(String, Type)>, TypeError> {
        // Check for conflicts
        let conflicts = self.check_mixin_field_conflicts(&mixin.fields, target_fields);
        if !conflicts.is_empty() {
            return Err(TypeError::Other(format!(
                "Mixin '{}' conflicts with {} on fields: {}",
                mixin.name,
                target_name,
                conflicts.join(", ")
            )));
        }

        // Merge fields
        let mut merged = target_fields.to_vec();
        merged.extend(mixin.fields.clone());
        Ok(merged)
    }

    /// Get all fields for a type including mixin fields (Feature #2201)
    pub fn get_all_fields(&mut self, type_name: &str) -> Vec<(String, Type)> {
        // Check if type has mixin compositions
        if let Some(mixin_refs) = self.compositions.get(type_name).cloned() {
            let mut all_fields = Vec::new();

            // Add mixin fields
            for mixin_ref in &mixin_refs {
                if let Some(mixin_info) = self.mixins.get(&mixin_ref.name).cloned() {
                    // Instantiate if generic
                    if !mixin_ref.type_args.is_empty() {
                        // Convert AST types to Type
                        let type_args: Vec<Type> = mixin_ref
                            .type_args
                            .iter()
                            .map(|ast_ty| self.ast_type_to_type(ast_ty))
                            .collect();
                        
                        if let Ok(instantiated) = mixin_info.instantiate(&type_args) {
                            all_fields.extend(instantiated.fields);
                        }
                    } else {
                        all_fields.extend(mixin_info.fields.clone());
                    }
                }
            }
            
            // TODO: Add class/struct own fields when they're registered
            all_fields
        } else {
            Vec::new()
        }
    }

    /// Resolve field access on a type, including mixin fields (Feature #2201)
    pub fn resolve_field(&mut self, type_name: &str, field_name: &str) -> Option<Type> {
        let all_fields = self.get_all_fields(type_name);
        all_fields
            .iter()
            .find(|(name, _)| name == field_name)
            .map(|(_, ty)| ty.clone())
    }
}



fn substitute_macro_template(
    input: &str,
    const_bindings: &std::collections::HashMap<String, String>,
) -> String {
    let mut output = input.to_string();
    for (key, value) in const_bindings {
        let needle = format!("{{{}}}", key);
        if output.contains(&needle) {
            output = output.replace(&needle, value);
        }
    }
    output
}

//==============================================================================
// Static Polymorphism: Interface Binding Resolution
//==============================================================================

/// Dispatch mode for trait method calls
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DispatchMode {
    /// Static dispatch: monomorphized, direct call (when binding exists)
    Static,
    /// Dynamic dispatch: vtable lookup (when no binding exists)
    Dynamic,
}

impl TypeChecker {
    /// Look up interface binding for a trait
    /// Returns Some(impl_type) if bound, None if not bound (dynamic dispatch)
    pub fn lookup_binding(&self, trait_name: &str) -> Option<&Type> {
        self.interface_bindings.get(trait_name)
    }

    /// Resolve a trait type through interface binding
    /// If bound: returns the implementation type (for static dispatch)
    /// If not bound: returns DynTrait (for dynamic dispatch)
    pub fn resolve_trait_type(&self, trait_name: &str) -> Type {
        match self.interface_bindings.get(trait_name) {
            Some(impl_type) => impl_type.clone(),
            None => Type::DynTrait(trait_name.to_string()),
        }
    }

    /// Determine dispatch mode for a trait
    /// Static if binding exists, Dynamic otherwise
    pub fn get_dispatch_mode(&self, trait_name: &str) -> DispatchMode {
        if self.interface_bindings.contains_key(trait_name) {
            DispatchMode::Static
        } else {
            DispatchMode::Dynamic
        }
    }

    /// Check if a binding is valid (implementation type actually implements the trait)
    pub fn is_valid_binding(&self, trait_name: &str) -> bool {
        if let Some(_impl_type) = self.interface_bindings.get(trait_name) {
            // Check that impl_type implements trait_name
            // For now, assume bindings are valid if the trait exists
            self.env.contains_key(trait_name)
        } else {
            false
        }
    }

    /// Get all interface bindings (for code generation)
    pub fn get_all_bindings(&self) -> &HashMap<String, Type> {
        &self.interface_bindings
    }
}
