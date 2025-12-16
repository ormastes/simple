impl Value {
    pub fn as_int(&self) -> Result<i64, CompileError> {
        match self {
            Value::Int(i) => Ok(*i),
            Value::Float(f) => Ok(*f as i64),
            Value::Bool(b) => Ok(if *b { 1 } else { 0 }),
            Value::Unit { value, .. } => value.as_int(),
            Value::Unique(u) => u.inner().as_int(),
            Value::Shared(s) => s.inner().as_int(),
            Value::Weak(w) => w.upgrade_inner().unwrap_or(Value::Nil).as_int(),
            Value::Handle(h) => h.resolve_inner().unwrap_or(Value::Nil).as_int(),
            Value::Borrow(b) => b.inner().as_int(),
            Value::BorrowMut(b) => b.inner().as_int(),
            Value::Str(_) => Err(CompileError::Semantic("expected int, got string".into())),
            Value::Symbol(_) => Err(CompileError::Semantic("expected int, got symbol".into())),
            Value::Nil => Ok(0),
            other => Err(CompileError::Semantic(format!(
                "expected int, got {other:?}"
            ))),
        }
    }

    pub fn as_float(&self) -> Result<f64, CompileError> {
        match self {
            Value::Float(f) => Ok(*f),
            Value::Int(i) => Ok(*i as f64),
            Value::Bool(b) => Ok(if *b { 1.0 } else { 0.0 }),
            Value::Unit { value, .. } => value.as_float(),
            Value::Unique(u) => u.inner().as_float(),
            Value::Shared(s) => s.inner().as_float(),
            Value::Weak(w) => w.upgrade_inner().unwrap_or(Value::Nil).as_float(),
            Value::Handle(h) => h.resolve_inner().unwrap_or(Value::Nil).as_float(),
            Value::Borrow(b) => b.inner().as_float(),
            Value::BorrowMut(b) => b.inner().as_float(),
            Value::Nil => Ok(0.0),
            other => Err(CompileError::Semantic(format!(
                "expected float, got {other:?}"
            ))),
        }
    }

    pub fn to_key_string(&self) -> String {
        match self {
            Value::Int(i) => i.to_string(),
            Value::Float(f) => f.to_string(),
            Value::Bool(b) => b.to_string(),
            Value::Str(s) => s.clone(),
            Value::Symbol(s) => s.clone(),
            Value::Unit { value, suffix, .. } => format!("{}_{}", value.to_key_string(), suffix),
            Value::Unique(u) => u.inner().to_key_string(),
            Value::Shared(s) => s.inner().to_key_string(),
            Value::Weak(w) => w.upgrade_inner().unwrap_or(Value::Nil).to_key_string(),
            Value::Handle(h) => h.resolve_inner().unwrap_or(Value::Nil).to_key_string(),
            Value::Borrow(b) => b.inner().to_key_string(),
            Value::BorrowMut(b) => b.inner().to_key_string(),
            Value::Nil => "nil".to_string(),
            other => format!("{other:?}"),
        }
    }

    pub fn truthy(&self) -> bool {
        match self {
            Value::Bool(b) => *b,
            Value::Int(i) => *i != 0,
            Value::Float(f) => *f != 0.0,
            Value::Str(s) => !s.is_empty(),
            Value::Symbol(_) => true,
            Value::Array(a) => !a.is_empty(),
            Value::Tuple(t) => !t.is_empty(),
            Value::Dict(d) => !d.is_empty(),
            Value::Nil => false,
            Value::Unit { value, .. } => value.truthy(),
            Value::Unique(u) => u.inner().truthy(),
            Value::Shared(s) => s.inner().truthy(),
            Value::Weak(w) => w.upgrade_inner().map_or(false, |v| v.truthy()),
            Value::Handle(h) => h.resolve_inner().map_or(false, |v| v.truthy()),
            Value::Borrow(b) => b.inner().truthy(),
            Value::BorrowMut(b) => b.inner().truthy(),
            Value::Object { .. }
            | Value::Enum { .. }
            | Value::Lambda { .. }
            | Value::BlockClosure { .. }
            | Value::Function { .. }
            | Value::Constructor { .. }
            | Value::TraitObject { .. }
            | Value::Actor(_)
            | Value::Future(_)
            | Value::Generator(_)
            | Value::Channel(_)
            | Value::ThreadPool(_)
            | Value::Mock(_)
            | Value::Matcher(_) => true,
        }
    }

    pub fn to_display_string(&self) -> String {
        match self {
            Value::Str(s) => s.clone(),
            Value::Symbol(s) => format!(":{s}"),
            Value::Int(i) => i.to_string(),
            Value::Float(f) => f.to_string(),
            Value::Bool(b) => b.to_string(),
            Value::Array(items) => {
                let parts: Vec<String> = items.iter().map(|v| v.to_display_string()).collect();
                format!("[{}]", parts.join(", "))
            }
            Value::Tuple(items) => {
                let parts: Vec<String> = items.iter().map(|v| v.to_display_string()).collect();
                format!("({})", parts.join(", "))
            }
            Value::Dict(map) => {
                let parts: Vec<String> = map
                    .iter()
                    .map(|(k, v)| format!("{}: {}", k, v.to_display_string()))
                    .collect();
                format!("{{{}}}", parts.join(", "))
            }
            Value::Nil => "nil".into(),
            Value::Unit { value, suffix, .. } => {
                format!("{}_{}", value.to_display_string(), suffix)
            }
            Value::Unique(u) => format!("&{}", u.inner().to_display_string()),
            Value::Shared(s) => format!("*{}", s.inner().to_display_string()),
            Value::Weak(w) => {
                if let Some(v) = w.upgrade_inner() {
                    format!("-{}", v.to_display_string())
                } else {
                    "-<dangling>".into()
                }
            }
            Value::Handle(h) => {
                if let Some(v) = h.resolve_inner() {
                    format!("+{}", v.to_display_string())
                } else {
                    "+<released>".into()
                }
            }
            Value::Borrow(b) => format!("&{}", b.inner().to_display_string()),
            Value::BorrowMut(b) => format!("&mut {}", b.inner().to_display_string()),
            other => format!("{other:?}"),
        }
    }

    /// Convert a unique pointer into its inner value (clone) for read-only operations.
    pub fn deref_pointer(self) -> Value {
        match self {
            Value::Unique(u) => u.into_inner(),
            Value::Shared(s) => s.into_inner(),
            Value::Weak(w) => w.upgrade_inner().unwrap_or(Value::Nil),
            Value::Handle(h) => h.resolve_inner().unwrap_or(Value::Nil),
            Value::Borrow(b) => b.inner().clone(),
            Value::BorrowMut(b) => b.inner().clone(),
            // Unit values pass through (they're not pointers)
            other => other,
        }
    }

    /// Get the runtime type name for this value (used for union type discrimination)
    pub fn type_name(&self) -> &'static str {
        match self {
            Value::Int(_) => "i64",
            Value::Float(_) => "f64",
            Value::Bool(_) => "bool",
            Value::Str(_) => "str",
            Value::Symbol(_) => "symbol",
            Value::Array(_) => "array",
            Value::Tuple(_) => "tuple",
            Value::Dict(_) => "dict",
            Value::Lambda { .. } => "function",
            Value::BlockClosure { .. } => "function",
            Value::Function { .. } => "function",
            Value::Object { .. } => "object",
            Value::Enum { .. } => "enum",
            Value::Constructor { .. } => "constructor",
            Value::TraitObject { .. } => "trait_object",
            Value::Unit { .. } => "unit",
            Value::Actor(_) => "actor",
            Value::Future(_) => "future",
            Value::Generator(_) => "generator",
            Value::Channel(_) => "channel",
            Value::ThreadPool(_) => "thread_pool",
            Value::Unique(_) => "unique",
            Value::Shared(_) => "shared",
            Value::Weak(_) => "weak",
            Value::Handle(_) => "handle",
            Value::Borrow(_) => "borrow",
            Value::BorrowMut(_) => "borrow_mut",
            Value::Mock(_) => "mock",
            Value::Matcher(_) => "matcher",
            Value::Nil => "nil",
        }
    }

    /// Check if this value matches a given type name (for union type discrimination)
    pub fn matches_type(&self, type_name: &str) -> bool {
        match type_name {
            // Integer types
            "i8" | "i16" | "i32" | "i64" | "u8" | "u16" | "u32" | "u64" | "int" | "Int" => {
                matches!(self, Value::Int(_))
            }
            // Float types
            "f32" | "f64" | "float" | "Float" => {
                matches!(self, Value::Float(_))
            }
            // Boolean
            "bool" | "Bool" => matches!(self, Value::Bool(_)),
            // String types
            "str" | "String" | "Str" => matches!(self, Value::Str(_)),
            // Nil/None
            "nil" | "Nil" | "None" => matches!(self, Value::Nil),
            // Array
            "array" | "Array" => matches!(self, Value::Array(_)),
            // Tuple
            "tuple" | "Tuple" => matches!(self, Value::Tuple(_)),
            // Dict
            "dict" | "Dict" => matches!(self, Value::Dict(_)),
            // Unit types - match by suffix
            "unit" | "Unit" => matches!(self, Value::Unit { .. }),
            // Check for object class name, enum name, or unit suffix
            _ => {
                if let Value::Object { class, .. } = self {
                    class == type_name
                } else if let Value::Enum { enum_name, .. } = self {
                    enum_name == type_name
                } else if let Value::Unit { suffix, .. } = self {
                    suffix == type_name
                } else {
                    false
                }
            }
        }
    }

    // ========================================================================
    // Option/Result enum constructors (reduce duplication across interpreter)
    // ========================================================================

    /// Create Option::Some(value)
    pub fn some(val: Value) -> Value {
        Value::Enum {
            enum_name: SpecialEnumType::Option.as_str().into(),
            variant: OptionVariant::Some.as_str().into(),
            payload: Some(Box::new(val)),
        }
    }

    /// Create Option::None
    pub fn none() -> Value {
        Value::Enum {
            enum_name: SpecialEnumType::Option.as_str().into(),
            variant: OptionVariant::None.as_str().into(),
            payload: None,
        }
    }

    /// Create Result::Ok(value)
    pub fn ok(val: Value) -> Value {
        Value::Enum {
            enum_name: SpecialEnumType::Result.as_str().into(),
            variant: ResultVariant::Ok.as_str().into(),
            payload: Some(Box::new(val)),
        }
    }

    /// Create Result::Err(value)
    pub fn err(val: Value) -> Value {
        Value::Enum {
            enum_name: SpecialEnumType::Result.as_str().into(),
            variant: ResultVariant::Err.as_str().into(),
            payload: Some(Box::new(val)),
        }
    }
}
