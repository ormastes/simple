impl TypeChecker {
    pub fn new() -> Self {
        let mut tc = Self {
            env: HashMap::new(),
            next_var: 0,
            type_params: HashMap::new(),
            subst: Substitution::new(),
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
        self.env.insert("print".to_string(), generic_fn.clone());
        self.env.insert("println".to_string(), generic_fn.clone());
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
}
