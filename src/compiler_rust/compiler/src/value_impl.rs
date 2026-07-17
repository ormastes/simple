/// Reserved marker tagging a `Dict` entry that bundles its original
/// (non-scalar) key alongside its value -- see `Value::wrap_dict_entry`.
/// Uses this codebase's existing double-underscore convention for reserved
/// internal names (`__setitem__`, `__getitem__`).
const DICT_ENTRY_MARKER: &str = "__dict_entry__";

/// Whether a stored dict value is a `wrap_dict_entry` marker tuple:
/// `Tuple([Symbol("__dict_entry__"), original_key, actual_value])`.
fn is_dict_entry_marker(items: &[Value]) -> bool {
    items.len() == 3 && matches!(&items[0], Value::Symbol(s) if s == DICT_ENTRY_MARKER)
}

impl Value {
    pub fn as_int(&self) -> Result<i64, CompileError> {
        match self {
            Value::Int(i) => Ok(*i),
            Value::UInt { value, .. } => Ok(*value as i64),
            Value::Float(f) => Ok(*f as i64),
            Value::Float32(f) => Ok(*f as i64),
            Value::Bool(b) => Ok(if *b { 1 } else { 0 }),
            Value::Unit { value, .. } => value.as_int(),
            Value::Unique(u) => u.inner().as_int(),
            Value::Shared(s) => s.inner().as_int(),
            Value::Weak(w) => w.upgrade_inner().unwrap_or(Value::Nil).as_int(),
            Value::Handle(h) => h.resolve_inner().unwrap_or(Value::Nil).as_int(),
            Value::Borrow(b) => b.inner().as_int(),
            Value::BorrowMut(b) => b.inner().as_int(),
            // Newtype wrapper: object with single `value` field auto-unwraps to inner.
            Value::Object { fields, .. } if fields.len() == 1 && fields.contains_key("value") => {
                fields.get("value").unwrap().as_int()
            }
            Value::Str(_) => {
                let ctx = ErrorContext::new()
                    .with_code(codes::TYPE_MISMATCH)
                    .with_help("expected integer type, got string");
                Err(CompileError::semantic_with_context(
                    "type mismatch: cannot convert string to int",
                    ctx,
                ))
            }
            Value::Symbol(_) => {
                let ctx = ErrorContext::new()
                    .with_code(codes::TYPE_MISMATCH)
                    .with_help("expected integer type, got symbol");
                Err(CompileError::semantic_with_context(
                    "type mismatch: cannot convert symbol to int",
                    ctx,
                ))
            }
            Value::Nil => Ok(0),
            other => {
                let actual_type = self.type_name();
                let ctx = ErrorContext::new()
                    .with_code(codes::TYPE_MISMATCH)
                    .with_help(format!("expected integer type, got {}", actual_type));
                Err(CompileError::semantic_with_context(
                    format!("type mismatch: cannot convert {} to int", actual_type),
                    ctx,
                ))
            }
        }
    }

    pub fn as_float(&self) -> Result<f64, CompileError> {
        match self {
            Value::Float(f) => Ok(*f),
            Value::Float32(f) => Ok(*f as f64),
            Value::Int(i) => Ok(*i as f64),
            Value::UInt { value, .. } => Ok(*value as f64),
            Value::Bool(b) => Ok(if *b { 1.0 } else { 0.0 }),
            Value::Unit { value, .. } => value.as_float(),
            Value::Unique(u) => u.inner().as_float(),
            Value::Shared(s) => s.inner().as_float(),
            Value::Weak(w) => w.upgrade_inner().unwrap_or(Value::Nil).as_float(),
            Value::Handle(h) => h.resolve_inner().unwrap_or(Value::Nil).as_float(),
            Value::Borrow(b) => b.inner().as_float(),
            Value::BorrowMut(b) => b.inner().as_float(),
            // Newtype wrapper: object with single `value` field auto-unwraps to inner.
            Value::Object { fields, .. } if fields.len() == 1 && fields.contains_key("value") => {
                fields.get("value").unwrap().as_float()
            }
            Value::Nil => Ok(0.0),
            other => {
                let actual_type = self.type_name();
                let ctx = ErrorContext::new()
                    .with_code(codes::TYPE_MISMATCH)
                    .with_help(format!("expected float type, got {}", actual_type));
                Err(CompileError::semantic_with_context(
                    format!("type mismatch: cannot convert {} to float", actual_type),
                    ctx,
                ))
            }
        }
    }

    pub fn to_key_string(&self) -> String {
        match self {
            Value::Int(i) => i.to_string(),
            Value::UInt { value, .. } => value.to_string(),
            Value::Float(f) => f.to_string(),
            Value::Float32(f) => f.to_string(),
            Value::Bool(b) => b.to_string(),
            Value::Str(s) => s.as_ref().clone(),
            Value::Symbol(s) => s.clone(),
            Value::Unit { value, suffix, .. } => format!("{}_{}", value.to_key_string(), suffix),
            Value::Unique(u) => u.inner().to_key_string(),
            Value::Shared(s) => s.inner().to_key_string(),
            Value::Weak(w) => w.upgrade_inner().unwrap_or(Value::Nil).to_key_string(),
            Value::Handle(h) => h.resolve_inner().unwrap_or(Value::Nil).to_key_string(),
            Value::Borrow(b) => b.inner().to_key_string(),
            Value::BorrowMut(b) => b.inner().to_key_string(),
            Value::NativeFunction(native) => format!("<native:{}>", native.name),
            Value::Nil => "nil".to_string(),
            // Composite keys: canonicalize instead of relying on the derived
            // `Debug` catch-all below. `fields` on `Value::Object` is an
            // `Arc<HashMap<String, Value>>`, and Rust's std `HashMap` seeds a
            // fresh, randomized hasher per instance -- two structurally equal
            // structs built as separate literals can iterate their fields in
            // a different order, so `format!("{:?}", ...)` is NOT a stable
            // function of value. That let two value-equal struct keys hash to
            // DIFFERENT dict-map keys, breaking key equality (root cause of
            // the over-count/duplicate-entry drift in
            // dict_struct_key_iteration_single_entry_2026-06-13). Sort field
            // names so the string is deterministic regardless of HashMap
            // iteration order.
            Value::Object { class, fields } => {
                let mut names: Vec<&String> = fields.keys().collect();
                names.sort();
                let parts: Vec<String> = names
                    .into_iter()
                    .map(|name| format!("{}={}", name, fields.get(name).unwrap().to_key_string()))
                    .collect();
                format!("{}{{{}}}", class, parts.join(","))
            }
            Value::Enum {
                enum_name,
                variant,
                payload,
            } => match payload {
                Some(p) => format!("{}::{}({})", enum_name, variant, p.to_key_string()),
                None => format!("{}::{}", enum_name, variant),
            },
            Value::Tuple(items) => {
                let parts: Vec<String> = items.iter().map(|v| v.to_key_string()).collect();
                format!("({})", parts.join(","))
            }
            Value::LabeledTuple { labels, values } => {
                let parts: Vec<String> = labels
                    .iter()
                    .zip(values.iter())
                    .map(|(l, v)| format!("{}={}", l, v.to_key_string()))
                    .collect();
                format!("({})", parts.join(","))
            }
            Value::Array(items) | Value::FrozenArray(items) => {
                let parts: Vec<String> = items.iter().map(|v| v.to_key_string()).collect();
                format!("[{}]", parts.join(","))
            }
            other => format!("{other:?}"),
        }
    }

    /// Whether `to_key_string()` on this value is a type-preserving round
    /// trip, i.e. the interpreter's `Dict` (a `HashMap<String, Value>`
    /// keyed by `to_key_string()`) never needs extra bookkeeping to hand
    /// the original key back on iteration. True for the scalar-ish types
    /// the interpreter's dict representation already handled correctly;
    /// false for composite types (struct/enum/tuple/array) whose
    /// `to_key_string()` is a canonical-but-lossy serialization.
    ///
    /// See `dict_struct_key_iteration_single_entry_2026-06-13`: iterating a
    /// struct-keyed `Dict` used to yield the map's raw string key (or crash
    /// on field access) instead of the original struct because the map
    /// value slot only ever stored the associated *value*, never the key.
    /// `wrap_dict_entry`/`unwrap_dict_entry`/`dict_entry_key_for_iteration`
    /// close that gap for non-scalar keys only, so scalar-keyed dict
    /// behavior (int/text/bool/float/nil) is completely unchanged.
    pub fn dict_key_is_scalar(&self) -> bool {
        match self {
            Value::Int(_)
            | Value::UInt { .. }
            | Value::Float(_)
            | Value::Float32(_)
            | Value::Bool(_)
            | Value::Str(_)
            | Value::Symbol(_)
            | Value::Nil => true,
            Value::Unit { value, .. } => value.dict_key_is_scalar(),
            Value::Unique(u) => u.inner().dict_key_is_scalar(),
            Value::Shared(s) => s.inner().dict_key_is_scalar(),
            Value::Weak(w) => w.upgrade_inner().unwrap_or(Value::Nil).dict_key_is_scalar(),
            Value::Handle(h) => h.resolve_inner().unwrap_or(Value::Nil).dict_key_is_scalar(),
            Value::Borrow(b) => b.inner().dict_key_is_scalar(),
            Value::BorrowMut(b) => b.inner().dict_key_is_scalar(),
            _ => false,
        }
    }

    /// Value stored in a `Dict`'s backing map for `key => value`. For
    /// self-describing (scalar) keys this is just `value` (unchanged
    /// behavior). For composite keys, the original `key` is bundled
    /// alongside `value` behind a reserved marker so it can be recovered
    /// later without a key argument on hand (dict iteration / `.keys()` /
    /// `.entries()`). The marker is a `Value::Symbol` with a
    /// double-underscore reserved name, mirroring this codebase's existing
    /// `__setitem__`/`__getitem__` convention for internal dunder names.
    pub fn wrap_dict_entry(key: &Value, value: Value) -> Value {
        if key.dict_key_is_scalar() {
            value
        } else {
            Value::Tuple(vec![Value::Symbol(DICT_ENTRY_MARKER.to_string()), key.clone(), value])
        }
    }

    /// Inverse of `wrap_dict_entry` for call sites that already know the
    /// key they looked up with (`get`, `contains`, `set`, ...).
    pub fn unwrap_dict_entry(key: &Value, stored: Value) -> Value {
        if key.dict_key_is_scalar() {
            return stored;
        }
        match stored {
            Value::Tuple(ref items) if is_dict_entry_marker(items) => items[2].clone(),
            other => other,
        }
    }

    /// Recover the original key from a stored dict entry when iterating
    /// blind (no key argument on hand: `for k, v in dict`, `.keys()`,
    /// `.entries()`). Falls back to the map's own string key -- today's
    /// (pre-existing, unchanged) behavior for scalar-keyed dicts.
    pub fn dict_entry_key_for_iteration(stored: &Value, string_key: &str) -> Value {
        match stored {
            Value::Tuple(items) if is_dict_entry_marker(items) => items[1].clone(),
            _ => Value::text(string_key.to_string()),
        }
    }

    /// Recover the original value from a stored dict entry when iterating
    /// blind.
    pub fn dict_entry_value_for_iteration(stored: &Value) -> Value {
        match stored {
            Value::Tuple(items) if is_dict_entry_marker(items) => items[2].clone(),
            other => other.clone(),
        }
    }

    pub fn truthy(&self) -> bool {
        match self {
            Value::Bool(b) => *b,
            Value::Int(i) => *i != 0,
            Value::UInt { value, .. } => *value != 0,
            Value::Float(f) => *f != 0.0,
            Value::Float32(f) => *f != 0.0,
            Value::Str(s) => !s.is_empty(),
            Value::Symbol(_) => true,
            Value::Array(a) => !a.is_empty(),
            Value::FrozenArray(a) => !a.is_empty(),
            Value::FixedSizeArray { data, .. } => !data.is_empty(),
            Value::Tuple(t) => !t.is_empty(),
            Value::LabeledTuple { values, .. } => !values.is_empty(),
            Value::Dict(d) => !d.is_empty(),
            Value::FrozenDict(d) => !d.is_empty(),
            Value::Nil => false,
            Value::Unit { value, .. } => value.truthy(),
            Value::Unique(u) => u.inner().truthy(),
            Value::Shared(s) => s.inner().truthy(),
            Value::Weak(w) => w.upgrade_inner().is_some_and(|v| v.truthy()),
            Value::Handle(h) => h.resolve_inner().is_some_and(|v| v.truthy()),
            Value::Borrow(b) => b.inner().truthy(),
            Value::BorrowMut(b) => b.inner().truthy(),
            Value::Union { inner, .. } => inner.truthy(),
            Value::Object { .. }
            | Value::Enum { .. }
            | Value::Lambda { .. }
            | Value::BlockClosure { .. }
            | Value::Function { .. }
            | Value::Constructor { .. }
            | Value::EnumType { .. }
            | Value::EnumVariantConstructor { .. }
            | Value::TraitType { .. }
            | Value::TraitObject { .. }
            | Value::Actor(_)
            | Value::Future(_)
            | Value::Generator(_)
            | Value::Channel(_)
            | Value::ThreadPool(_)
            | Value::Mock(_)
            | Value::Matcher(_)
            | Value::NativeFunction(_)
            | Value::Block { .. } => true,
        }
    }

    pub fn to_display_string(&self) -> String {
        match self {
            Value::Str(s) => s.as_ref().clone(),
            Value::Symbol(s) => format!(":{s}"),
            Value::Int(i) => i.to_string(),
            Value::UInt { value, .. } => value.to_string(),
            Value::Float(f) => f.to_string(),
            Value::Float32(f) => f.to_string(),
            Value::Bool(b) => b.to_string(),
            Value::Array(items) => {
                let parts: Vec<String> = items.iter().map(|v| v.to_display_string()).collect();
                format!("[{}]", parts.join(", "))
            }
            Value::FrozenArray(items) => {
                let parts: Vec<String> = items.iter().map(|v| v.to_display_string()).collect();
                format!("[{}]", parts.join(", "))
            }
            Value::FixedSizeArray { size, data } => {
                let parts: Vec<String> = data.iter().map(|v| v.to_display_string()).collect();
                format!("[{}; {}]", parts.join(", "), size)
            }
            Value::Tuple(items) => {
                let parts: Vec<String> = items.iter().map(|v| v.to_display_string()).collect();
                format!("({})", parts.join(", "))
            }
            Value::LabeledTuple { labels, values } => {
                let parts: Vec<String> = labels
                    .iter()
                    .zip(values.iter())
                    .map(|(label, value)| format!("{label}: {}", value.to_display_string()))
                    .collect();
                format!("({})", parts.join(", "))
            }
            Value::Dict(map) => {
                let parts: Vec<String> = map
                    .iter()
                    .map(|(k, v)| format!("{}: {}", k, v.to_display_string()))
                    .collect();
                format!("{{{}}}", parts.join(", "))
            }
            Value::FrozenDict(map) => {
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
            Value::NativeFunction(native) => format!("<native:{}>", native.name),
            Value::Object { class, fields } => {
                let parts: Vec<String> = fields
                    .iter()
                    .map(|(k, v)| format!("{}: {}", k, v.to_display_string()))
                    .collect();
                format!("{}({})", class, parts.join(", "))
            }
            Value::Enum {
                enum_name,
                variant,
                payload,
            } => {
                if let Some(val) = payload {
                    format!("{}::{}({})", enum_name, variant, val.to_display_string())
                } else {
                    format!("{}::{}", enum_name, variant)
                }
            }
            Value::Block { kind, payload, result } => {
                if let Some(res) = result {
                    res.to_display_string()
                } else {
                    crate::blocks::display_block(kind, payload)
                }
            }
            Value::Lambda { .. } => "<lambda>".into(),
            Value::BlockClosure { .. } => "<block_closure>".into(),
            Value::Function { name, .. } => format!("<fn:{}>", name),
            Value::Constructor { class_name } => format!("<constructor:{}>", class_name),
            Value::EnumType { enum_name } => format!("<enum:{}>", enum_name),
            Value::EnumVariantConstructor { .. } => "<enum_variant_constructor>".into(),
            Value::TraitType { .. } => "<trait_type>".into(),
            Value::TraitObject { .. } => "<trait_object>".into(),
            Value::Union { inner, .. } => inner.to_display_string(),
            Value::Actor(_) => "<actor>".into(),
            Value::Future(_) => "<future>".into(),
            Value::Generator(_) => "<generator>".into(),
            Value::Channel(_) => "<channel>".into(),
            Value::ThreadPool(_) => "<thread_pool>".into(),
            Value::Mock(_) => "<mock>".into(),
            Value::Matcher(_) => "<matcher>".into(),
        }
    }

    /// Convert to debug string with type information (for dbg() and debug_fmt())
    pub fn to_debug_string(&self) -> String {
        match self {
            Value::Str(s) => format!("{:?}", s),
            Value::Int(i) => format!("{}i64", i),
            Value::Float(f) => format!("{}f64", f),
            Value::Float32(f) => format!("{}f32", f),
            Value::Bool(b) => format!("{}", b),
            Value::Symbol(s) => format!(":{}", s),
            Value::Nil => "nil".into(),
            Value::Object { class, fields } => {
                let parts: Vec<String> = fields
                    .iter()
                    .map(|(k, v)| format!("{}: {}", k, v.to_debug_string()))
                    .collect();
                format!("{}({})", class, parts.join(", "))
            }
            Value::Enum {
                enum_name,
                variant,
                payload,
            } => {
                if let Some(val) = payload {
                    format!("{}::{}({})", enum_name, variant, val.to_debug_string())
                } else {
                    format!("{}::{}", enum_name, variant)
                }
            }
            Value::Block { kind, payload, .. } => {
                format!("Block({}, {:?})", kind, payload)
            }
            Value::Array(items) => {
                let parts: Vec<String> = items.iter().map(|v| v.to_debug_string()).collect();
                format!("[{}]", parts.join(", "))
            }
            Value::Dict(map) => {
                let parts: Vec<String> = map
                    .iter()
                    .map(|(k, v)| format!("{}: {}", k, v.to_debug_string()))
                    .collect();
                format!("{{{}}}", parts.join(", "))
            }
            _ => format!("{} = {}", self.type_name(), self.to_display_string()),
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
            Value::UInt { width, .. } => match *width {
                8 => "u8",
                16 => "u16",
                32 => "u32",
                64 => "u64",
                _ => "uint",
            },
            Value::Float(_) => "f64",
            Value::Float32(_) => "f32",
            Value::Bool(_) => "bool",
            Value::Str(_) => "str",
            Value::Symbol(_) => "symbol",
            Value::Array(_) => "array",
            Value::FrozenArray(_) => "array",
            Value::FixedSizeArray { .. } => "array",
            Value::Tuple(_) | Value::LabeledTuple { .. } => "tuple",
            Value::Dict(_) => "dict",
            Value::FrozenDict(_) => "dict",
            Value::Lambda { .. } => "function",
            Value::BlockClosure { .. } => "function",
            Value::Function { .. } => "function",
            Value::NativeFunction(_) => "function",
            Value::Object { .. } => "object",
            Value::Enum { .. } => "enum",
            Value::Union { inner, .. } => inner.type_name(),
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
            Value::EnumType { .. } => "enum_type",
            Value::EnumVariantConstructor { .. } => "enum_variant_constructor",
            Value::TraitType { .. } => "trait_type",
            Value::Block { .. } => "block",
            Value::Nil => "nil",
        }
    }

    /// Get the abstract value kind from hir-core.
    ///
    /// This provides a unified type abstraction shared with the runtime.
    pub fn value_kind(&self) -> simple_runtime::hir_core::ValueKind {
        use simple_runtime::hir_core::ValueKind;
        match self {
            Value::Int(_) => ValueKind::Int,
            Value::UInt { .. } => ValueKind::Int,
            Value::Float(_) => ValueKind::Float,
            Value::Float32(_) => ValueKind::Float,
            Value::Bool(_) => ValueKind::Bool,
            Value::Str(_) => ValueKind::String,
            Value::Symbol(_) => ValueKind::Symbol,
            Value::Array(_) => ValueKind::Array,
            Value::FrozenArray(_) => ValueKind::Array,
            Value::FixedSizeArray { .. } => ValueKind::Array,
            Value::Tuple(_) | Value::LabeledTuple { .. } => ValueKind::Tuple,
            Value::Dict(_) => ValueKind::Dict,
            Value::FrozenDict(_) => ValueKind::Dict,
            Value::Lambda { .. } => ValueKind::Closure,
            Value::BlockClosure { .. } => ValueKind::BlockClosure,
            Value::Function { .. } => ValueKind::Closure,
            Value::NativeFunction(_) => ValueKind::NativeFunction,
            Value::Object { .. } => ValueKind::Object,
            Value::Enum { .. } => ValueKind::Enum,
            Value::Union { inner, .. } => inner.value_kind(),
            Value::Constructor { .. } => ValueKind::Constructor,
            Value::TraitObject { .. } => ValueKind::TraitObject,
            Value::Unit { .. } => ValueKind::Unit,
            Value::Actor(_) => ValueKind::Actor,
            Value::Future(_) => ValueKind::Future,
            Value::Generator(_) => ValueKind::Generator,
            Value::Channel(_) => ValueKind::Channel,
            Value::ThreadPool(_) => ValueKind::ThreadPool,
            Value::Unique(_) => ValueKind::Unique,
            Value::Shared(_) => ValueKind::Shared,
            Value::Weak(_) => ValueKind::Weak,
            Value::Handle(_) => ValueKind::Handle,
            Value::Borrow(_) => ValueKind::Borrow,
            Value::BorrowMut(_) => ValueKind::BorrowMut,
            Value::Mock(_) => ValueKind::Mock,
            Value::Matcher(_) => ValueKind::Matcher,
            Value::EnumType { .. } => ValueKind::EnumType,
            Value::EnumVariantConstructor { .. } => ValueKind::EnumVariantConstructor,
            Value::TraitType { .. } => ValueKind::TraitType,
            Value::Block { .. } => ValueKind::Block,
            Value::Nil => ValueKind::Nil,
            Value::FrozenArray(_) => ValueKind::Array,
            Value::FrozenDict(_) => ValueKind::Dict,
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
            "f64" => matches!(self, Value::Float(_)),
            "f32" => matches!(self, Value::Float32(_)),
            "float" | "Float" => matches!(self, Value::Float(_) | Value::Float32(_)),
            // Boolean
            "bool" | "Bool" => matches!(self, Value::Bool(_)),
            // String types
            "str" | "String" | "Str" => matches!(self, Value::Str(_)),
            // Nil/None
            "nil" | "Nil" | "None" => matches!(self, Value::Nil),
            // Array
            "array" | "Array" => matches!(self, Value::Array(_)),
            // Tuple
            "tuple" | "Tuple" => matches!(self, Value::Tuple(_) | Value::LabeledTuple { .. }),
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
                } else if matches!(self, Value::NativeFunction(_)) {
                    type_name == "function" || type_name == "Function"
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
