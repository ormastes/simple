use super::*;
use std::collections::HashMap;

//==============================================================================
// Struct Layout (for zero-cost field access like C++/Rust)
//==============================================================================

/// Memory layout information for a struct type.
/// Enables zero-cost field access through compile-time offset computation.
///
/// Layout follows C ABI rules:
/// - Fields are aligned to their natural alignment
/// - Struct is padded to its largest member alignment
/// - vtable pointer (if present) is at offset 0
#[derive(Debug, Clone, PartialEq)]
pub struct StructLayout {
    /// Type name
    pub name: String,
    /// Field information: (name, type_id, byte_offset, size)
    pub fields: Vec<FieldLayout>,
    /// Total size of the struct in bytes (including padding)
    pub size: u32,
    /// Alignment requirement in bytes
    pub alignment: u8,
    /// Whether this struct has a vtable pointer (for virtual dispatch)
    pub has_vtable: bool,
    /// Class/struct ID for runtime type identification
    pub type_id: u32,
}

/// Layout information for a single field
#[derive(Debug, Clone, PartialEq)]
pub struct FieldLayout {
    /// Field name
    pub name: String,
    /// Field type
    pub ty: TypeId,
    /// Byte offset from struct start (after vtable if present)
    pub offset: u32,
    /// Size of the field in bytes
    pub size: u32,
}

impl StructLayout {
    /// Create a new struct layout with computed offsets.
    /// Uses C ABI rules for alignment and padding.
    pub fn new(
        name: String,
        fields: &[(String, TypeId)],
        registry: &TypeRegistry,
        has_vtable: bool,
        type_id: u32,
    ) -> Self {
        let mut field_layouts = Vec::with_capacity(fields.len());
        let mut current_offset: u32 = if has_vtable { 8 } else { 0 }; // vtable ptr is 8 bytes
        let mut max_align: u8 = if has_vtable { 8 } else { 1 };

        for (field_name, field_ty) in fields {
            let (size, align) = Self::type_size_align(*field_ty, registry);

            // Align current offset
            let align_u32 = align as u32;
            let padding = (align_u32 - (current_offset % align_u32)) % align_u32;
            current_offset += padding;

            field_layouts.push(FieldLayout {
                name: field_name.clone(),
                ty: *field_ty,
                offset: current_offset,
                size,
            });

            current_offset += size;
            max_align = max_align.max(align);
        }

        // Pad struct to alignment
        let max_align_u32 = max_align as u32;
        let final_padding = (max_align_u32 - (current_offset % max_align_u32)) % max_align_u32;
        let total_size = current_offset + final_padding;

        Self {
            name,
            fields: field_layouts,
            size: total_size,
            alignment: max_align,
            has_vtable,
            type_id,
        }
    }

    /// Get size and alignment for a type (C ABI rules)
    fn type_size_align(ty: TypeId, _registry: &TypeRegistry) -> (u32, u8) {
        match ty {
            TypeId::VOID => (0, 1),
            TypeId::BOOL => (1, 1),
            TypeId::I8 | TypeId::U8 => (1, 1),
            TypeId::I16 | TypeId::U16 => (2, 2),
            TypeId::I32 | TypeId::U32 => (4, 4),
            TypeId::I64 | TypeId::U64 => (8, 8),
            TypeId::F32 => (4, 4),
            TypeId::F64 => (8, 8),
            TypeId::STRING => (8, 8), // Pointer to string
            TypeId::NIL => (8, 8),    // Tagged value
            _ => (8, 8),              // Default to pointer size for custom types
        }
    }

    /// Get field offset by index (O(1))
    pub fn field_offset(&self, index: usize) -> Option<u32> {
        self.fields.get(index).map(|f| f.offset)
    }

    /// Get field offset by name (O(n))
    pub fn field_offset_by_name(&self, name: &str) -> Option<u32> {
        self.fields.iter().find(|f| f.name == name).map(|f| f.offset)
    }

    /// Get field index by name
    pub fn field_index(&self, name: &str) -> Option<usize> {
        self.fields.iter().position(|f| f.name == name)
    }
}

/// Registry of struct layouts for all types in a module
#[derive(Debug, Default)]
pub struct LayoutRegistry {
    layouts: HashMap<TypeId, StructLayout>,
    name_to_type: HashMap<String, TypeId>,
    next_type_id: u32,
}

impl LayoutRegistry {
    pub fn new() -> Self {
        Self {
            layouts: HashMap::new(),
            name_to_type: HashMap::new(),
            next_type_id: 0,
        }
    }

    /// Register a struct layout and return its runtime type ID
    pub fn register(&mut self, type_id: TypeId, layout: StructLayout) -> u32 {
        let runtime_id = self.next_type_id;
        self.next_type_id += 1;
        self.name_to_type.insert(layout.name.clone(), type_id);
        self.layouts.insert(type_id, layout);
        runtime_id
    }

    /// Get layout for a type
    pub fn get(&self, type_id: TypeId) -> Option<&StructLayout> {
        self.layouts.get(&type_id)
    }

    /// Get layout by name
    pub fn get_by_name(&self, name: &str) -> Option<&StructLayout> {
        self.name_to_type.get(name).and_then(|id| self.layouts.get(id))
    }
}
