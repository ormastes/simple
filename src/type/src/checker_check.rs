impl TypeChecker {
    /// Helper to check match arms (pattern binding, guard, and body statements)
    fn check_match_arms(&mut self, arms: &[simple_parser::ast::MatchArm]) -> Result<(), TypeError> {
        for arm in arms {
            self.bind_pattern(&arm.pattern);
            if let Some(guard) = &arm.guard {
                let _ = self.infer_expr(guard)?;
            }
            for stmt in &arm.body.statements {
                self.check_node(stmt)?;
            }
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
                }
                Node::Actor(a) => {
                    // Register actor as a type
                    let ty = self.fresh_var();
                    self.env.insert(a.name.clone(), ty);
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
            }
        }
        // Second pass: check all nodes
        for item in items {
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
                for stmt in &func.body.statements {
                    self.check_node(stmt)?;
                }
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
                for stmt in &if_stmt.then_block.statements {
                    self.check_node(stmt)?;
                }
                for (cond, block) in &if_stmt.elif_branches {
                    let _ = self.infer_expr(cond)?;
                    for stmt in &block.statements {
                        self.check_node(stmt)?;
                    }
                }
                if let Some(block) = &if_stmt.else_block {
                    for stmt in &block.statements {
                        self.check_node(stmt)?;
                    }
                }
                Ok(())
            }
            Node::While(while_stmt) => {
                let _ = self.infer_expr(&while_stmt.condition)?;
                // Handle while let pattern binding
                if let Some(pattern) = &while_stmt.let_pattern {
                    self.bind_pattern(pattern);
                }
                for stmt in &while_stmt.body.statements {
                    self.check_node(stmt)?;
                }
                Ok(())
            }
            Node::For(for_stmt) => {
                let _ = self.infer_expr(&for_stmt.iterable)?;
                if let Pattern::Identifier(name) = &for_stmt.pattern {
                    let ty = self.fresh_var();
                    self.env.insert(name.clone(), ty);
                }
                for stmt in &for_stmt.body.statements {
                    self.check_node(stmt)?;
                }
                Ok(())
            }
            Node::Loop(loop_stmt) => {
                for stmt in &loop_stmt.body.statements {
                    self.check_node(stmt)?;
                }
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
                    for stmt in &method.body.statements {
                        self.check_node(stmt)?;
                    }
                    self.env = old_env;
                }
                Ok(())
            }
            Node::Impl(impl_block) => {
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
                    for stmt in &method.body.statements {
                        self.check_node(stmt)?;
                    }
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
                for stmt in &with_stmt.body.statements {
                    self.check_node(stmt)?;
                }
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
}
