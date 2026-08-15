// ============================================================================
// Manual Memory Pointer Wrappers
// ============================================================================

#[derive(Debug)]
pub struct ManualUniqueValue {
    ptr: ManualUnique<Value>,
}

impl ManualUniqueValue {
    pub fn new(value: Value) -> Self {
        MANUAL_GC.with(|gc| Self { ptr: gc.alloc(value) })
    }

    pub fn inner(&self) -> &Value {
        &self.ptr
    }

    pub fn into_inner(self) -> Value {
        self.ptr.into_inner()
    }

    /// Get a mutable reference to the inner value (update functionality)
    pub fn inner_mut(&mut self) -> &mut Value {
        &mut self.ptr
    }
}

impl Clone for ManualUniqueValue {
    fn clone(&self) -> Self {
        // Cloning a unique pointer duplicates the underlying value into a fresh unique owner.
        Self::new((*self.ptr).clone())
    }
}

impl PartialEq for ManualUniqueValue {
    fn eq(&self, other: &Self) -> bool {
        self.inner() == other.inner()
    }
}

#[derive(Debug)]
pub struct ManualSharedValue {
    ptr: ManualShared<Value>,
}

impl ManualSharedValue {
    pub fn new(value: Value) -> Self {
        MANUAL_GC.with(|gc| Self {
            ptr: gc.alloc_shared(value),
        })
    }

    pub fn inner(&self) -> &Value {
        &self.ptr
    }

    pub fn into_inner(self) -> Value {
        (*self.ptr).clone()
    }

    pub fn downgrade(&self) -> ManualWeak<Value> {
        self.ptr.downgrade()
    }
}

impl Clone for ManualSharedValue {
    fn clone(&self) -> Self {
        Self { ptr: self.ptr.clone() }
    }
}

impl PartialEq for ManualSharedValue {
    fn eq(&self, other: &Self) -> bool {
        self.inner() == other.inner()
    }
}

pub struct ManualWeakValue {
    ptr: ManualWeak<Value>,
}

impl fmt::Debug for ManualWeakValue {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("ManualWeakValue")
    }
}

impl ManualWeakValue {
    pub fn new_from_shared(shared: &ManualSharedValue) -> Self {
        Self {
            ptr: shared.downgrade(),
        }
    }

    pub fn upgrade_inner(&self) -> Option<Value> {
        self.ptr.upgrade().map(|s| (*s).clone())
    }
}

impl Clone for ManualWeakValue {
    fn clone(&self) -> Self {
        Self { ptr: self.ptr.clone() }
    }
}

impl PartialEq for ManualWeakValue {
    fn eq(&self, other: &Self) -> bool {
        self.upgrade_inner() == other.upgrade_inner()
    }
}

pub struct ManualHandleValue {
    handle: ManualHandle<Value>,
}

impl fmt::Debug for ManualHandleValue {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("ManualHandleValue")
    }
}

impl ManualHandleValue {
    pub fn new(value: Value) -> Self {
        let pool = ManualHandlePool::new();
        Self {
            handle: pool.alloc(value),
        }
    }

    pub fn resolve_inner(&self) -> Option<Value> {
        self.handle.resolve().map(|v| (*v).clone())
    }
}

impl Clone for ManualHandleValue {
    fn clone(&self) -> Self {
        Self {
            handle: self.handle.clone(),
        }
    }
}

impl PartialEq for ManualHandleValue {
    fn eq(&self, other: &Self) -> bool {
        self.resolve_inner() == other.resolve_inner()
    }
}

// ============================================================================
// Borrow Types (Runtime Borrow Checking)
// ============================================================================

/// Macro to implement common borrow wrapper functionality.
/// Reduces duplication between BorrowValue and BorrowMutValue.
macro_rules! impl_borrow_wrapper {
    ($name:ident, $doc:expr) => {
        #[doc = $doc]
        #[derive(Debug)]
        pub struct $name {
            /// The borrowed value (shared via Arc + RwLock for thread-safe runtime checking)
            inner: Arc<RwLock<Value>>,
        }

        impl $name {
            pub fn new(value: Value) -> Self {
                Self {
                    inner: Arc::new(RwLock::new(value)),
                }
            }

            pub fn from_arc(arc: Arc<RwLock<Value>>) -> Self {
                Self { inner: arc }
            }

            pub fn inner(&self) -> std::sync::RwLockReadGuard<'_, Value> {
                self.inner.read().unwrap()
            }

            pub fn get_arc(&self) -> Arc<RwLock<Value>> {
                self.inner.clone()
            }
        }

        impl Clone for $name {
            fn clone(&self) -> Self {
                // Cloning a borrow shares the same underlying reference
                Self {
                    inner: self.inner.clone(),
                }
            }
        }

        impl PartialEq for $name {
            fn eq(&self, other: &Self) -> bool {
                *self.inner.read().unwrap() == *other.inner.read().unwrap()
            }
        }
    };
}

impl_borrow_wrapper!(
    BorrowValue,
    "Immutable borrow - uses RwLock for thread-safe runtime borrow checking.\n\
     Multiple immutable borrows are allowed simultaneously."
);

impl_borrow_wrapper!(
    BorrowMutValue,
    "Mutable borrow - uses RwLock for thread-safe runtime borrow checking.\n\
     Only one mutable borrow is allowed at a time (enforced at runtime via RwLock)."
);

// Additional method only for mutable borrows
impl BorrowMutValue {
    pub fn inner_mut(&self) -> std::sync::RwLockWriteGuard<'_, Value> {
        self.inner.write().unwrap()
    }
}

impl Clone for Value {
    fn clone(&self) -> Self {
        match self {
            Value::Int(i) => Value::Int(*i),
            Value::UInt { value, width } => Value::UInt {
                value: *value,
                width: *width,
            },
            Value::Float(f) => Value::Float(*f),
            Value::Float32(f) => Value::Float32(*f),
            Value::Bool(b) => Value::Bool(*b),
            Value::Str(s) => Value::shared_text(Arc::clone(s)),
            Value::StrBytes(b) => Value::StrBytes(Arc::clone(b)),
            Value::Symbol(s) => Value::Symbol(s.clone()),
            Value::Array(a) => Value::Array(Arc::clone(a)),
            Value::ByteArray(a) => Value::ByteArray(Arc::clone(a)),
            Value::FrozenArray(a) => Value::FrozenArray(a.clone()),
            Value::FrozenByteArray(a) => Value::FrozenByteArray(Arc::clone(a)),
            Value::FixedSizeArray { size, data } => Value::FixedSizeArray {
                size: *size,
                data: data.clone(),
            },
            Value::Tuple(t) => Value::Tuple(t.clone()),
            Value::LabeledTuple { labels, values } => Value::LabeledTuple {
                labels: labels.clone(),
                values: values.clone(),
            },
            Value::Dict(d) => Value::Dict(Arc::clone(d)),
            Value::FrozenDict(d) => Value::FrozenDict(d.clone()),
            Value::Lambda { params, body, env } => Value::Lambda {
                params: params.clone(),
                body: body.clone(),
                env: Arc::clone(env),
            },
            Value::BlockClosure { nodes, env } => Value::BlockClosure {
                nodes: nodes.clone(),
                env: Arc::clone(env),
            },
            Value::Function {
                name,
                def,
                captured_env,
            } => Value::Function {
                name: name.clone(),
                def: def.clone(),
                captured_env: captured_env.clone(),
            },
            Value::Object { class, fields } => Value::Object {
                class: class.clone(),
                fields: Arc::clone(fields),
            },
            Value::ClassInstance(instance) => Value::ClassInstance(Arc::clone(instance)),
            Value::Enum {
                enum_name,
                variant,
                payload,
            } => Value::Enum {
                enum_name: enum_name.clone(),
                variant: variant.clone(),
                payload: payload.clone(),
            },
            Value::Union { type_index, inner } => Value::Union {
                type_index: *type_index,
                inner: inner.clone(),
            },
            Value::Constructor { class_name } => Value::Constructor {
                class_name: class_name.clone(),
            },
            Value::EnumType { enum_name } => Value::EnumType {
                enum_name: enum_name.clone(),
            },
            Value::EnumVariantConstructor {
                enum_name,
                variant_name,
            } => Value::EnumVariantConstructor {
                enum_name: enum_name.clone(),
                variant_name: variant_name.clone(),
            },
            Value::TraitType { trait_name } => Value::TraitType {
                trait_name: trait_name.clone(),
            },
            Value::TraitObject { trait_name, inner } => Value::TraitObject {
                trait_name: trait_name.clone(),
                inner: inner.clone(),
            },
            Value::Unit { value, suffix, family } => Value::Unit {
                value: value.clone(),
                suffix: suffix.clone(),
                family: family.clone(),
            },
            Value::Actor(handle) => Value::Actor(handle.clone()),
            Value::Future(f) => Value::Future(f.clone()),
            Value::Generator(g) => Value::Generator(g.clone()),
            Value::Channel(c) => Value::Channel(c.clone()),
            Value::ThreadPool(tp) => Value::ThreadPool(tp.clone()),
            Value::Unique(u) => Value::Unique(u.clone()),
            Value::Shared(s) => Value::Shared(s.clone()),
            Value::Weak(w) => Value::Weak(w.clone()),
            Value::Handle(h) => Value::Handle(h.clone()),
            Value::Borrow(b) => Value::Borrow(b.clone()),
            Value::BorrowMut(b) => Value::BorrowMut(b.clone()),
            Value::Mock(m) => Value::Mock(m.clone()),
            Value::Matcher(m) => Value::Matcher(m.clone()),
            Value::NativeFunction(native) => Value::NativeFunction(native.clone()),
            Value::Block { kind, payload, result } => Value::Block {
                kind: kind.clone(),
                payload: payload.clone(),
                result: result.clone(),
            },
            Value::ByteArray(bytes) => Value::ByteArray(Arc::clone(bytes)),
            Value::FrozenArray(arr) => Value::FrozenArray(Arc::clone(arr)),
            Value::FrozenByteArray(bytes) => Value::FrozenByteArray(Arc::clone(bytes)),
            Value::FrozenDict(dict) => Value::FrozenDict(Arc::clone(dict)),
            Value::Nil => Value::Nil,
        }
    }
}

impl PartialEq for Value {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Value::Int(a), Value::Int(b)) => a == b,
            (Value::UInt { value: a, .. }, Value::UInt { value: b, .. }) => a == b,
            // Cross-variant: UInt vs Int compares by mathematical magnitude.
            // Negative signed values never equal an unsigned value.
            (Value::UInt { value, .. }, Value::Int(b)) | (Value::Int(b), Value::UInt { value, .. }) => {
                *b >= 0 && *value == *b as u64
            }
            (Value::Float(a), Value::Float(b)) => a == b,
            (Value::Float32(a), Value::Float32(b)) => a == b,
            // Cross-variant: f32 vs f64 compares as f64 (widening)
            (Value::Float32(a), Value::Float(b)) | (Value::Float(b), Value::Float32(a)) => (*a as f64) == *b,
            // Cross-variant: int vs float compares numerically
            (Value::Float32(a), Value::Int(b)) | (Value::Int(b), Value::Float32(a)) => (*a as f64) == (*b as f64),
            (Value::Bool(a), Value::Bool(b)) => a == b,
            (Value::Str(a), Value::Str(b)) => a == b,
            // Byte-wise text equality across the raw-fragment variant.
            (Value::StrBytes(a), Value::StrBytes(b)) => a == b,
            (Value::Str(a), Value::StrBytes(b)) => a.as_bytes() == b.as_slice(),
            (Value::StrBytes(a), Value::Str(b)) => a.as_slice() == b.as_bytes(),
            (Value::Symbol(a), Value::Symbol(b)) => a == b,
            (Value::Array(a), Value::Array(b)) => a == b,
            (Value::ByteArray(a), Value::ByteArray(b))
            | (Value::ByteArray(a), Value::FrozenByteArray(b))
            | (Value::FrozenByteArray(a), Value::ByteArray(b))
            | (Value::FrozenByteArray(a), Value::FrozenByteArray(b)) => a == b,
            (Value::ByteArray(a), Value::Array(b))
            | (Value::FrozenByteArray(a), Value::Array(b))
            | (Value::ByteArray(a), Value::FrozenArray(b))
            | (Value::FrozenByteArray(a), Value::FrozenArray(b)) => packed_bytes_equal_values(a, b),
            (Value::Array(a), Value::ByteArray(b))
            | (Value::Array(a), Value::FrozenByteArray(b))
            | (Value::FrozenArray(a), Value::ByteArray(b))
            | (Value::FrozenArray(a), Value::FrozenByteArray(b)) => packed_bytes_equal_values(b, a),
            (Value::Tuple(a), Value::Tuple(b)) => a == b,
            (Value::LabeledTuple { labels: la, values: va }, Value::LabeledTuple { labels: lb, values: vb }) => {
                la == lb && va == vb
            }
            (Value::Tuple(a), Value::LabeledTuple { values: b, .. })
            | (Value::LabeledTuple { values: a, .. }, Value::Tuple(b)) => a == b,
            (Value::Dict(a), Value::Dict(b)) => a == b,
            (
                Value::Lambda {
                    params: pa,
                    body: ba,
                    env: ea,
                },
                Value::Lambda {
                    params: pb,
                    body: bb,
                    env: eb,
                },
            ) => pa == pb && ba == bb && ea == eb,
            (
                Value::Function {
                    name: na,
                    def: da,
                    captured_env: ea,
                },
                Value::Function {
                    name: nb,
                    def: db,
                    captured_env: eb,
                },
            ) => na == nb && da == db && ea == eb,
            (Value::Object { class: ca, fields: fa }, Value::Object { class: cb, fields: fb }) => ca == cb && fa == fb,
            (
                Value::Enum {
                    enum_name: ea,
                    variant: va,
                    payload: pa,
                },
                Value::Enum {
                    enum_name: eb,
                    variant: vb,
                    payload: pb,
                },
            ) => ea == eb && va == vb && pa == pb,
            (Value::Constructor { class_name: a }, Value::Constructor { class_name: b }) => a == b,
            (Value::Actor(_), Value::Actor(_)) => true,
            (Value::Future(a), Value::Future(b)) => a == b,
            (Value::Unique(a), Value::Unique(b)) => a == b,
            (Value::Shared(a), Value::Shared(b)) => a == b,
            (Value::Weak(a), Value::Weak(b)) => a == b,
            (Value::Handle(a), Value::Handle(b)) => a == b,
            (Value::Borrow(a), Value::Borrow(b)) => a == b,
            (Value::BorrowMut(a), Value::BorrowMut(b)) => a == b,
            (
                Value::Unit {
                    value: va,
                    suffix: sa,
                    family: fa,
                },
                Value::Unit {
                    value: vb,
                    suffix: sb,
                    family: fb,
                },
            ) => va == vb && sa == sb && fa == fb,
            (Value::NativeFunction(_), Value::NativeFunction(_)) => false,
            (
                Value::Block {
                    kind: ka,
                    payload: pa,
                    result: ra,
                },
                Value::Block {
                    kind: kb,
                    payload: pb,
                    result: rb,
                },
            ) => ka == kb && pa == pb && ra == rb,
            (Value::Nil, Value::Nil) => true,
            _ => false,
        }
    }
}

fn packed_bytes_equal_values(bytes: &[u8], values: &[Value]) -> bool {
    bytes.len() == values.len()
        && bytes.iter().zip(values).all(|(byte, value)| match value {
            Value::UInt { value, .. } => *value == u64::from(*byte),
            Value::Int(value) => *value == i64::from(*byte),
            _ => false,
        })
}

#[cfg(test)]
mod packed_byte_tests {
    use super::*;

    #[test]
    fn packed_bytes_preserve_legacy_array_equality() {
        let packed = Value::byte_array(vec![0, 127, 255]);
        let legacy = Value::array(vec![
            Value::Int(0),
            Value::UInt { value: 127, width: 8 },
            Value::Int(255),
        ]);
        assert_eq!(packed, legacy);
        assert_ne!(Value::byte_array(vec![1]), Value::array(vec![Value::Int(257)]));
    }

    #[test]
    fn packed_byte_clone_is_copy_on_write_and_frozen_bytes_extract() {
        let original = Value::byte_array(vec![1, 2, 3]);
        let mut changed = original.clone();
        let Value::ByteArray(bytes) = &mut changed else { panic!("packed clone changed kind") };
        Arc::make_mut(bytes)[0] = 9;
        assert_eq!(original.byte_array_view(), Some([1, 2, 3].as_slice()));
        assert_eq!(changed.byte_array_view(), Some([9, 2, 3].as_slice()));
        assert_eq!(Value::frozen_byte_array(vec![4, 5]).try_array_bytes(), Some(vec![4, 5]));
    }
}
