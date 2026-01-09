//! Tagged Union Types (Algebraic Data Types)
//!
//! This module implements tagged unions (also known as sum types or variant types)
//! which are more expressive than simple enums. Each variant can have associated data.
//!
//! Example:
//! ```simple
//! union Shape:
//!     Circle(radius: f64)
//!     Rectangle(width: f64, height: f64)
//!     Triangle(a: f64, b: f64, c: f64)
//! ```

use std::collections::HashMap;

/// A variant in a tagged union type
#[derive(Debug, Clone, PartialEq)]
pub struct UnionVariant {
    /// Variant name (e.g., "Circle", "Rectangle")
    pub name: String,
    /// Associated data fields (name -> type)
    pub fields: Vec<(String, crate::Type)>,
    /// Discriminant value (tag) for this variant
    pub discriminant: u32,
}

/// Tagged union type definition
#[derive(Debug, Clone, PartialEq)]
pub struct TaggedUnion {
    /// Union type name
    pub name: String,
    /// Variants in this union
    pub variants: Vec<UnionVariant>,
    /// Optional type parameters for generic unions (e.g., Option<T>)
    pub type_params: Vec<String>,
}

impl TaggedUnion {
    /// Create a new tagged union
    pub fn new(name: String) -> Self {
        Self {
            name,
            variants: Vec::new(),
            type_params: Vec::new(),
        }
    }

    /// Add a variant to this union
    pub fn add_variant(&mut self, variant: UnionVariant) {
        self.variants.push(variant);
    }

    /// Get a variant by name
    pub fn get_variant(&self, name: &str) -> Option<&UnionVariant> {
        self.variants.iter().find(|v| v.name == name)
    }

    /// Get the number of variants
    pub fn variant_count(&self) -> usize {
        self.variants.len()
    }

    /// Check if this is a generic union
    pub fn is_generic(&self) -> bool {
        !self.type_params.is_empty()
    }

    /// Check if all variants are exhaustively handled in a match
    pub fn check_exhaustiveness(&self, handled_variants: &[String]) -> Vec<String> {
        let handled: std::collections::HashSet<_> = handled_variants.iter().collect();
        self.variants
            .iter()
            .filter(|v| !handled.contains(&v.name))
            .map(|v| v.name.clone())
            .collect()
    }
}

impl UnionVariant {
    /// Create a new variant
    pub fn new(name: String, discriminant: u32) -> Self {
        Self {
            name,
            fields: Vec::new(),
            discriminant,
        }
    }

    /// Add a field to this variant
    pub fn add_field(&mut self, name: String, ty: crate::Type) {
        self.fields.push((name, ty));
    }

    /// Get the number of fields
    pub fn field_count(&self) -> usize {
        self.fields.len()
    }

    /// Check if this is a unit variant (no fields)
    pub fn is_unit(&self) -> bool {
        self.fields.is_empty()
    }

    /// Get field type by name
    pub fn get_field_type(&self, name: &str) -> Option<&crate::Type> {
        self.fields
            .iter()
            .find(|(n, _)| n == name)
            .map(|(_, ty)| ty)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::Type;

    #[test]
    fn test_create_tagged_union() {
        let mut shape_union = TaggedUnion::new("Shape".to_string());

        let mut circle = UnionVariant::new("Circle".to_string(), 0);
        circle.add_field("radius".to_string(), Type::Float);
        shape_union.add_variant(circle);

        let mut rectangle = UnionVariant::new("Rectangle".to_string(), 1);
        rectangle.add_field("width".to_string(), Type::Float);
        rectangle.add_field("height".to_string(), Type::Float);
        shape_union.add_variant(rectangle);

        assert_eq!(shape_union.variant_count(), 2);
        assert!(shape_union.get_variant("Circle").is_some());
        assert!(shape_union.get_variant("Rectangle").is_some());
        assert!(shape_union.get_variant("Triangle").is_none());
    }

    #[test]
    fn test_exhaustiveness_check() {
        let mut shape_union = TaggedUnion::new("Shape".to_string());
        shape_union.add_variant(UnionVariant::new("Circle".to_string(), 0));
        shape_union.add_variant(UnionVariant::new("Rectangle".to_string(), 1));
        shape_union.add_variant(UnionVariant::new("Triangle".to_string(), 2));

        let handled = vec!["Circle".to_string(), "Rectangle".to_string()];
        let missing = shape_union.check_exhaustiveness(&handled);

        assert_eq!(missing, vec!["Triangle".to_string()]);
    }

    #[test]
    fn test_generic_union() {
        let mut option_union = TaggedUnion::new("Option".to_string());
        option_union.type_params.push("T".to_string());

        let mut some_variant = UnionVariant::new("Some".to_string(), 0);
        some_variant.add_field("value".to_string(), Type::TypeParam("T".to_string()));
        option_union.add_variant(some_variant);

        option_union.add_variant(UnionVariant::new("None".to_string(), 1));

        assert!(option_union.is_generic());
        assert_eq!(option_union.variant_count(), 2);
    }
}
