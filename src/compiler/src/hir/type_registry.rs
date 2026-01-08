// Type ID allocator and registry for HIR types module
// (imports are inherited from parent types.rs)

/// Type ID allocator for formal verification.
///
/// Separates ID allocation from type storage, making allocation semantics explicit:
/// - `alloc()` always returns a fresh ID (monotonically increasing)
/// - No ID reuse is possible
///
/// Lean equivalent:
/// ```lean
/// structure TypeIdAllocator := (next : Nat)
///
/// def alloc (a : TypeIdAllocator) : TypeId × TypeIdAllocator :=
///   (TypeId.mk a.next, { next := a.next + 1 })
/// ```
#[derive(Debug, Clone)]
pub struct TypeIdAllocator {
    next: u32,
}

impl TypeIdAllocator {
    /// Create a new allocator starting after built-in types.
    pub fn new() -> Self {
        Self { next: 14 } // Built-in types 0-13
    }

    /// Create an allocator with a custom starting ID.
    pub fn with_start(start: u32) -> Self {
        Self { next: start }
    }

    /// Allocate a fresh TypeId.
    /// Invariant: returned ID is always unique and greater than any previous allocation.
    pub fn alloc(&mut self) -> TypeId {
        let id = TypeId(self.next);
        self.next += 1;
        id
    }

    /// Get the next ID that would be allocated (for debugging/verification).
    pub fn peek_next(&self) -> u32 {
        self.next
    }
}

impl Default for TypeIdAllocator {
    fn default() -> Self {
        Self::new()
    }
}

/// Type registry that maps TypeId to HirType
#[derive(Debug, Default)]
pub struct TypeRegistry {
    types: HashMap<TypeId, HirType>,
    allocator: TypeIdAllocator,
    name_to_id: HashMap<String, TypeId>,
}

impl TypeRegistry {
    pub fn new() -> Self {
        let mut registry = Self {
            types: HashMap::new(),
            allocator: TypeIdAllocator::new(),
            name_to_id: HashMap::new(),
        };

        // Register built-in types
        registry.types.insert(TypeId::VOID, HirType::Void);
        registry.types.insert(TypeId::BOOL, HirType::Bool);
        registry.types.insert(TypeId::I8, HirType::signed_int(8));
        registry.types.insert(TypeId::I16, HirType::signed_int(16));
        registry.types.insert(TypeId::I32, HirType::signed_int(32));
        registry.types.insert(TypeId::I64, HirType::signed_int(64));
        registry.types.insert(TypeId::U8, HirType::unsigned_int(8));
        registry
            .types
            .insert(TypeId::U16, HirType::unsigned_int(16));
        registry
            .types
            .insert(TypeId::U32, HirType::unsigned_int(32));
        registry
            .types
            .insert(TypeId::U64, HirType::unsigned_int(64));
        registry
            .types
            .insert(TypeId::F32, HirType::Float { bits: 32 });
        registry
            .types
            .insert(TypeId::F64, HirType::Float { bits: 64 });
        registry.types.insert(TypeId::STRING, HirType::String);
        registry.types.insert(TypeId::NIL, HirType::Nil);

        // Register type names (lowercase with bit-width)
        registry.name_to_id.insert("void".to_string(), TypeId::VOID);
        registry.name_to_id.insert("bool".to_string(), TypeId::BOOL);
        registry.name_to_id.insert("i8".to_string(), TypeId::I8);
        registry.name_to_id.insert("i16".to_string(), TypeId::I16);
        registry.name_to_id.insert("i32".to_string(), TypeId::I32);
        registry.name_to_id.insert("i64".to_string(), TypeId::I64);
        registry.name_to_id.insert("u8".to_string(), TypeId::U8);
        registry.name_to_id.insert("u16".to_string(), TypeId::U16);
        registry.name_to_id.insert("u32".to_string(), TypeId::U32);
        registry.name_to_id.insert("u64".to_string(), TypeId::U64);
        registry.name_to_id.insert("f16".to_string(), TypeId::F32); // f16 maps to f32 for now
        registry.name_to_id.insert("f32".to_string(), TypeId::F32);
        registry.name_to_id.insert("f64".to_string(), TypeId::F64);
        registry
            .name_to_id
            .insert("str".to_string(), TypeId::STRING);
        registry.name_to_id.insert("nil".to_string(), TypeId::NIL);

        registry
    }

    pub fn register(&mut self, ty: HirType) -> TypeId {
        let id = self.allocator.alloc();
        self.types.insert(id, ty);
        id
    }

    /// Get the allocator for inspection (useful for verification).
    pub fn allocator(&self) -> &TypeIdAllocator {
        &self.allocator
    }

    pub fn register_named(&mut self, name: String, ty: HirType) -> TypeId {
        let id = self.register(ty);
        self.name_to_id.insert(name, id);
        id
    }

    pub fn get(&self, id: TypeId) -> Option<&HirType> {
        self.types.get(&id)
    }

    /// Get the element type of an array type
    pub fn get_array_element(&self, id: TypeId) -> Option<TypeId> {
        match self.types.get(&id) {
            Some(HirType::Array { element, .. }) => Some(*element),
            _ => None,
        }
    }

    pub fn lookup(&self, name: &str) -> Option<TypeId> {
        self.name_to_id.get(name).copied()
    }

    /// Register a type alias - maps a name to an existing type ID
    /// Used for simple type aliases and refined types (CTR-020)
    pub fn register_alias(&mut self, name: String, type_id: TypeId) {
        self.name_to_id.insert(name, type_id);
    }

    /// Check if a type is snapshot-safe for use in old() expressions (CTR-060-062)
    ///
    /// Snapshot-safe types can be safely captured at function entry and compared
    /// in postconditions. These include:
    /// - CTR-060: Primitives (bool, integers, floats)
    /// - CTR-060: Nil type
    /// - CTR-060: Enums (captured by discriminant)
    /// - CTR-061: Immutable value types (structs with no mutable references)
    ///
    /// Types that are NOT snapshot-safe:
    /// - Mutable references
    /// - Types containing mutable state
    /// - Function types
    /// - Unknown types
    pub fn is_snapshot_safe(&self, type_id: TypeId) -> bool {
        match self.get(type_id) {
            Some(HirType::Void) => true,
            Some(HirType::Bool) => true,
            Some(HirType::Int { .. }) => true,
            Some(HirType::Float { .. }) => true,
            Some(HirType::String) => true, // Strings are immutable
            Some(HirType::Nil) => true,
            Some(HirType::Enum { .. }) => true, // Enums captured by discriminant

            // Tuples are safe if all elements are safe
            Some(HirType::Tuple(elements)) => {
                elements.iter().all(|e| self.is_snapshot_safe(*e))
            }

            // Arrays are safe if elements are safe (assuming immutable array)
            Some(HirType::Array { element, .. }) => self.is_snapshot_safe(*element),

            // SIMD vectors are safe if elements are safe (always primitive types)
            Some(HirType::Simd { element, .. }) => self.is_snapshot_safe(*element),

            // Unit types are snapshot-safe (they're constrained primitives)
            Some(HirType::UnitType { .. }) => true,

            // Union types are snapshot-safe if all variants are snapshot-safe
            Some(HirType::Union { variants }) => {
                variants.iter().all(|v| self.is_snapshot_safe(*v))
            }

            // Mixins are snapshot-safe if all fields are snapshot-safe
            Some(HirType::Mixin { fields, .. }) => {
                fields.iter().all(|(_, ty)| self.is_snapshot_safe(*ty))
            }

            // CTR-061: Structs are snapshot-safe if all fields are snapshot-safe
            // CTR-062: Structs with #[snapshot] attribute have custom snapshot semantics
            Some(HirType::Struct { fields, has_snapshot, .. }) => {
                // If marked with #[snapshot], always consider it snapshot-safe
                if *has_snapshot {
                    return true;
                }
                // Otherwise, check all fields recursively
                fields.iter().all(|(_, ty)| self.is_snapshot_safe(*ty))
            }

            // Pointers are only safe if they're immutable borrows
            Some(HirType::Pointer { kind, capability: _, inner }) => {
                matches!(kind, PointerKind::Borrow) && self.is_snapshot_safe(*inner)
            }

            // Functions and unknown types are not snapshot-safe
            Some(HirType::Function { .. }) => false,
            Some(HirType::Unknown) => false,
            None => false,
        }
    }

    /// Get the name of a struct/class/enum type for invariant lookup (CTR-012)
    ///
    /// Returns the type name if the type is a named type (struct, class, enum),
    /// otherwise returns None.
    pub fn get_type_name(&self, type_id: TypeId) -> Option<&str> {
        match self.get(type_id) {
            Some(HirType::Struct { name, .. }) => Some(name.as_str()),
            Some(HirType::Enum { name, .. }) => Some(name.as_str()),
            _ => None,
        }
    }
}
