impl TypeChecker {
    pub fn new() -> Self {
        let mut tc = Self {
            env: HashMap::new(),
            next_var: 0,
            type_params: HashMap::new(),
            subst: Substitution::new(),
            macros: HashMap::new(),
            available_macros: HashSet::new(),
            next_ref_id: 0,
            trait_impls: HashMap::new(),
        };
        // Add built-in functions to environment
        tc.add_builtins();
        tc
    }

    /// Add built-in functions to the type environment
    fn add_builtins(&mut self) {
        // Generate fresh vars first to avoid borrow issues
        let var1 = self.fresh_var();
        let var2 = self.fresh_var();
        let var3 = self.fresh_var();
        let var4 = self.fresh_var();
        let var5 = self.fresh_var();
        let var6 = self.fresh_var();
        let var7 = self.fresh_var();
        let var8 = self.fresh_var();
        let var9 = self.fresh_var();
        let var10 = self.fresh_var();
        let var11 = self.fresh_var();
        let var12 = self.fresh_var();
        let var13 = self.fresh_var();

        // Generic function type (takes any, returns any)
        let generic_fn = Type::Function {
            params: vec![var1.clone()],
            ret: Box::new(var2),
        };

        // Concurrency functions
        self.env.insert("spawn".to_string(), generic_fn.clone());
        self.env.insert("spawn_isolated".to_string(), generic_fn.clone());
        self.env.insert("async".to_string(), generic_fn.clone());
        self.env.insert("future".to_string(), generic_fn.clone());
        self.env.insert("await".to_string(), generic_fn.clone());
        self.env.insert(
            "is_ready".to_string(),
            Type::Function {
                params: vec![var3],
                ret: Box::new(Type::Bool),
            },
        );

        // Actor functions
        self.env.insert(
            "send".to_string(),
            Type::Function {
                params: vec![var4, var5],
                ret: Box::new(Type::Nil),
            },
        );
        self.env.insert("recv".to_string(), generic_fn.clone());
        self.env.insert(
            "reply".to_string(),
            Type::Function {
                params: vec![var6],
                ret: Box::new(Type::Nil),
            },
        );
        self.env.insert(
            "join".to_string(),
            Type::Function {
                params: vec![var7],
                ret: Box::new(Type::Nil),
            },
        );

        // Common built-in functions
        self.env.insert(
            "len".to_string(),
            Type::Function {
                params: vec![var8],
                ret: Box::new(Type::Int),
            },
        );
        // I/O prelude functions
        self.env.insert("print".to_string(), generic_fn.clone());
        self.env.insert("println".to_string(), generic_fn.clone());
        self.env.insert("eprint".to_string(), generic_fn.clone());
        self.env.insert("eprintln".to_string(), generic_fn.clone());
        self.env.insert("input".to_string(), generic_fn.clone());
        // Channel type constructor
        self.env.insert("Channel".to_string(), generic_fn.clone());
        // ThreadPool constructor
        self.env.insert("ThreadPool".to_string(), generic_fn.clone());
        self.env.insert(
            "type".to_string(),
            Type::Function {
                params: vec![var9],
                ret: Box::new(Type::Str),
            },
        );
        self.env.insert(
            "str".to_string(),
            Type::Function {
                params: vec![var10],
                ret: Box::new(Type::Str),
            },
        );
        self.env.insert(
            "int".to_string(),
            Type::Function {
                params: vec![var11],
                ret: Box::new(Type::Int),
            },
        );

        // Math functions (extern)
        self.env.insert(
            "abs".to_string(),
            Type::Function {
                params: vec![Type::Int],
                ret: Box::new(Type::Int),
            },
        );
        self.env.insert(
            "sqrt".to_string(),
            Type::Function {
                params: vec![Type::Int],
                ret: Box::new(Type::Int),
            },
        );
        self.env.insert(
            "pow".to_string(),
            Type::Function {
                params: vec![Type::Int, Type::Int],
                ret: Box::new(Type::Int),
            },
        );
        self.env.insert(
            "min".to_string(),
            Type::Function {
                params: vec![Type::Int, Type::Int],
                ret: Box::new(Type::Int),
            },
        );
        self.env.insert(
            "max".to_string(),
            Type::Function {
                params: vec![Type::Int, Type::Int],
                ret: Box::new(Type::Int),
            },
        );

        // Generator/coroutine functions
        self.env.insert("generator".to_string(), generic_fn.clone());
        self.env.insert("next".to_string(), generic_fn.clone());
        self.env.insert("collect".to_string(), generic_fn.clone());

        // Use remaining vars for reserved names
        let _ = (var12, var13);
    }

    pub fn fresh_var(&mut self) -> Type {
        let id = self.next_var;
        self.next_var += 1;
        Type::Var(id)
    }

    //==========================================================================
    // Let-Polymorphism (matches Generics.lean)
    //==========================================================================
    // These functions implement Algorithm W style let-polymorphism:
    // - instantiate: Replace bound vars with fresh vars (for using a polymorphic value)
    // - generalize: Collect free vars to create a scheme (for let-binding)
    //
    // Lean equivalents (from Generics.lean):
    // ```lean
    // def instantiate (sch : Scheme) (st : FreshState) : (Ty × FreshState)
    // def generalize (envFreeVars : List TyVar) (t : Ty) : Scheme
    // ```

    /// Instantiate a type scheme by replacing bound variables with fresh ones
    /// Lean: def instantiate (sch : Scheme) (st : FreshState) : (Ty × FreshState)
    pub fn instantiate(&mut self, scheme: &TypeScheme) -> Type {
        if scheme.vars.is_empty() {
            return scheme.ty.clone();
        }

        // Create a mapping from bound vars to fresh vars
        let mut var_map = HashMap::new();
        for &bound_var in &scheme.vars {
            let fresh = self.fresh_var();
            if let Type::Var(fresh_id) = fresh {
                var_map.insert(bound_var, fresh_id);
            }
        }

        // Apply the mapping to the type body
        self.instantiate_type(&scheme.ty, &var_map)
    }

    fn instantiate_type(&self, ty: &Type, var_map: &HashMap<usize, usize>) -> Type {
        match ty {
            Type::Var(id) => {
                if let Some(&new_id) = var_map.get(id) {
                    Type::Var(new_id)
                } else {
                    ty.clone()
                }
            }
            Type::Function { params, ret } => Type::Function {
                params: params.iter().map(|p| self.instantiate_type(p, var_map)).collect(),
                ret: Box::new(self.instantiate_type(ret, var_map)),
            },
            Type::Array(elem) => Type::Array(Box::new(self.instantiate_type(elem, var_map))),
            Type::Union(types) => Type::Union(
                types.iter().map(|t| self.instantiate_type(t, var_map)).collect()
            ),
            Type::Generic { name, args } => Type::Generic {
                name: name.clone(),
                args: args.iter().map(|a| self.instantiate_type(a, var_map)).collect(),
            },
            Type::Tuple(types) => Type::Tuple(
                types.iter().map(|t| self.instantiate_type(t, var_map)).collect()
            ),
            Type::Dict { key, value } => Type::Dict {
                key: Box::new(self.instantiate_type(key, var_map)),
                value: Box::new(self.instantiate_type(value, var_map)),
            },
            Type::Optional(inner) => Type::Optional(Box::new(self.instantiate_type(inner, var_map))),
            Type::Borrow(inner) => Type::Borrow(Box::new(self.instantiate_type(inner, var_map))),
            Type::BorrowMut(inner) => Type::BorrowMut(Box::new(self.instantiate_type(inner, var_map))),
            Type::Simd { lanes, element } => Type::Simd {
                lanes: *lanes,
                element: Box::new(self.instantiate_type(element, var_map)),
            },
            _ => ty.clone(),
        }
    }

    /// Collect free type variables in a type (not in the environment)
    fn free_vars(&self, ty: &Type) -> Vec<usize> {
        let mut vars = Vec::new();
        self.collect_free_vars(ty, &mut vars);
        vars.sort();
        vars.dedup();
        vars
    }

    fn collect_free_vars(&self, ty: &Type, vars: &mut Vec<usize>) {
        match ty {
            Type::Var(id) => vars.push(*id),
            Type::Function { params, ret } => {
                for p in params {
                    self.collect_free_vars(p, vars);
                }
                self.collect_free_vars(ret, vars);
            }
            Type::Array(elem) => self.collect_free_vars(elem, vars),
            Type::Union(types) => {
                for t in types {
                    self.collect_free_vars(t, vars);
                }
            }
            Type::Generic { args, .. } => {
                for a in args {
                    self.collect_free_vars(a, vars);
                }
            }
            Type::Tuple(types) => {
                for t in types {
                    self.collect_free_vars(t, vars);
                }
            }
            Type::Dict { key, value } => {
                self.collect_free_vars(key, vars);
                self.collect_free_vars(value, vars);
            }
            Type::Optional(inner) => self.collect_free_vars(inner, vars),
            Type::Borrow(inner) => self.collect_free_vars(inner, vars),
            Type::BorrowMut(inner) => self.collect_free_vars(inner, vars),
            Type::Simd { element, .. } => self.collect_free_vars(element, vars),
            _ => {}
        }
    }

    /// Collect free type variables in the environment
    fn env_free_vars(&self) -> Vec<usize> {
        let mut vars = Vec::new();
        for ty in self.env.values() {
            let resolved = ty.apply_subst(&self.subst);
            self.collect_free_vars(&resolved, &mut vars);
        }
        vars.sort();
        vars.dedup();
        vars
    }

    /// Generalize a type over free variables not in environment
    /// Lean: def generalize (envFreeVars : List TyVar) (t : Ty) : Scheme
    pub fn generalize(&self, ty: &Type) -> TypeScheme {
        let resolved_ty = ty.apply_subst(&self.subst);
        let ty_free = self.free_vars(&resolved_ty);
        let env_free = self.env_free_vars();

        // Variables to quantify are those free in ty but not in env
        let to_generalize: Vec<usize> = ty_free
            .into_iter()
            .filter(|v| !env_free.contains(v))
            .collect();

        TypeScheme {
            vars: to_generalize,
            ty: resolved_ty,
        }
    }
}
