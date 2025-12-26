// ============================================================================
// Manual Memory Pointer Wrappers
// ============================================================================

#[derive(Debug)]
pub struct ManualUniqueValue {
    ptr: ManualUnique<Value>,
}

impl ManualUniqueValue {
    pub fn new(value: Value) -> Self {
        MANUAL_GC.with(|gc| Self {
            ptr: gc.alloc(value),
        })
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
        Self {
            ptr: self.ptr.clone(),
        }
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
        Self {
            ptr: self.ptr.clone(),
        }
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
            Value::Float(f) => Value::Float(*f),
            Value::Bool(b) => Value::Bool(*b),
            Value::Str(s) => Value::Str(s.clone()),
            Value::Symbol(s) => Value::Symbol(s.clone()),
            Value::Array(a) => Value::Array(a.clone()),
            Value::Tuple(t) => Value::Tuple(t.clone()),
            Value::Dict(d) => Value::Dict(d.clone()),
            Value::Lambda { params, body, env } => Value::Lambda {
                params: params.clone(),
                body: body.clone(),
                env: env.clone(),
            },
            Value::BlockClosure { nodes, env } => Value::BlockClosure {
                nodes: nodes.clone(),
                env: env.clone(),
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
                fields: fields.clone(),
            },
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
            Value::TraitObject { trait_name, inner } => Value::TraitObject {
                trait_name: trait_name.clone(),
                inner: inner.clone(),
            },
            Value::Unit {
                value,
                suffix,
                family,
            } => Value::Unit {
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
            Value::Nil => Value::Nil,
        }
    }
}

impl PartialEq for Value {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Value::Int(a), Value::Int(b)) => a == b,
            (Value::Float(a), Value::Float(b)) => a == b,
            (Value::Bool(a), Value::Bool(b)) => a == b,
            (Value::Str(a), Value::Str(b)) => a == b,
            (Value::Symbol(a), Value::Symbol(b)) => a == b,
            (Value::Array(a), Value::Array(b)) => a == b,
            (Value::Tuple(a), Value::Tuple(b)) => a == b,
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
            (
                Value::Object {
                    class: ca,
                    fields: fa,
                },
                Value::Object {
                    class: cb,
                    fields: fb,
                },
            ) => ca == cb && fa == fb,
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
            (Value::Nil, Value::Nil) => true,
            _ => false,
        }
    }
}
