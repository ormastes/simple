//! Bitfield Types
//!
//! This module implements bitfield types for compact data representation
//! and hardware register access.
//!
//! Example:
//! ```simple
//! bitfield StatusReg(u32):
//!     enabled: 1       # bit 0
//!     mode: 2          # bits 1-2
//!     priority: 4      # bits 3-6
//!     reserved: 25     # bits 7-31
//! ```

use std::collections::HashMap;

/// Integer type used for bitfield backing storage
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BackingType {
    U8,
    U16,
    U32,
    U64,
    U128,
}

impl BackingType {
    /// Get the bit width of this backing type
    pub fn bit_width(&self) -> u32 {
        match self {
            BackingType::U8 => 8,
            BackingType::U16 => 16,
            BackingType::U32 => 32,
            BackingType::U64 => 64,
            BackingType::U128 => 128,
        }
    }

    /// Parse backing type from string
    pub fn from_str(s: &str) -> Option<Self> {
        match s {
            "u8" => Some(BackingType::U8),
            "u16" => Some(BackingType::U16),
            "u32" => Some(BackingType::U32),
            "u64" => Some(BackingType::U64),
            "u128" => Some(BackingType::U128),
            _ => None,
        }
    }

    /// Convert to type name
    pub fn to_str(&self) -> &'static str {
        match self {
            BackingType::U8 => "u8",
            BackingType::U16 => "u16",
            BackingType::U32 => "u32",
            BackingType::U64 => "u64",
            BackingType::U128 => "u128",
        }
    }
}

/// A field in a bitfield
#[derive(Debug, Clone, PartialEq)]
pub struct BitfieldField {
    /// Field name
    pub name: String,
    /// Bit offset (starting position)
    pub offset: u32,
    /// Number of bits
    pub width: u32,
    /// Whether this field is reserved (not accessible)
    pub is_reserved: bool,
}

impl BitfieldField {
    /// Create a new bitfield field
    pub fn new(name: String, offset: u32, width: u32) -> Self {
        let is_reserved = name.starts_with('_');
        Self {
            name,
            offset,
            width,
            is_reserved,
        }
    }

    /// Get the bit mask for this field
    pub fn mask(&self) -> u128 {
        if self.width >= 128 {
            u128::MAX
        } else {
            ((1u128 << self.width) - 1) << self.offset
        }
    }

    /// Extract value from backing integer
    pub fn extract(&self, backing: u128) -> u128 {
        (backing >> self.offset) & ((1u128 << self.width) - 1)
    }

    /// Insert value into backing integer
    pub fn insert(&self, backing: u128, value: u128) -> u128 {
        let mask = self.mask();
        let shifted = (value << self.offset) & mask;
        (backing & !mask) | shifted
    }

    /// Check if a value fits in this field
    pub fn fits(&self, value: u128) -> bool {
        if self.width >= 128 {
            true
        } else {
            value < (1u128 << self.width)
        }
    }
}

/// Bitfield type definition
#[derive(Debug, Clone, PartialEq)]
pub struct Bitfield {
    /// Bitfield type name
    pub name: String,
    /// Backing integer type
    pub backing: BackingType,
    /// Fields in declaration order
    pub fields: Vec<BitfieldField>,
    /// Field lookup by name
    field_map: HashMap<String, usize>,
}

impl Bitfield {
    /// Create a new bitfield
    pub fn new(name: String, backing: BackingType) -> Self {
        Self {
            name,
            backing,
            fields: Vec::new(),
            field_map: HashMap::new(),
        }
    }

    /// Add a field to this bitfield
    pub fn add_field(&mut self, name: String, width: u32) -> Result<(), String> {
        // Calculate offset
        let offset = self.total_bits();

        // Check if field fits
        if offset + width > self.backing.bit_width() {
            return Err(format!(
                "Field '{}' doesn't fit: {} bits used, {} bits available",
                name,
                offset + width,
                self.backing.bit_width()
            ));
        }

        // Check for duplicate names
        if !name.starts_with('_') && self.field_map.contains_key(&name) {
            return Err(format!("Duplicate field name '{}'", name));
        }

        let field = BitfieldField::new(name.clone(), offset, width);
        let idx = self.fields.len();
        self.fields.push(field);

        if !name.starts_with('_') {
            self.field_map.insert(name, idx);
        }

        Ok(())
    }

    /// Get total bits used by all fields
    pub fn total_bits(&self) -> u32 {
        self.fields.iter().map(|f| f.width).sum()
    }

    /// Get remaining bits
    pub fn remaining_bits(&self) -> u32 {
        self.backing.bit_width() - self.total_bits()
    }

    /// Get a field by name
    pub fn get_field(&self, name: &str) -> Option<&BitfieldField> {
        self.field_map.get(name).map(|&idx| &self.fields[idx])
    }

    /// Check if this bitfield is fully defined (all bits assigned)
    pub fn is_complete(&self) -> bool {
        self.total_bits() == self.backing.bit_width()
    }

    /// Validate bitfield layout
    pub fn validate(&self) -> Result<(), String> {
        let total = self.total_bits();
        let available = self.backing.bit_width();

        if total > available {
            return Err(format!(
                "Bitfield '{}' uses {} bits but backing type {} has only {} bits",
                self.name,
                total,
                self.backing.to_str(),
                available
            ));
        }

        // Check for overlapping fields
        let mut used_bits = vec![false; available as usize];
        for field in &self.fields {
            for bit in field.offset..(field.offset + field.width) {
                if used_bits[bit as usize] {
                    return Err(format!("Overlapping bits at position {}", bit));
                }
                used_bits[bit as usize] = true;
            }
        }

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_backing_type_bit_width() {
        assert_eq!(BackingType::U8.bit_width(), 8);
        assert_eq!(BackingType::U16.bit_width(), 16);
        assert_eq!(BackingType::U32.bit_width(), 32);
        assert_eq!(BackingType::U64.bit_width(), 64);
        assert_eq!(BackingType::U128.bit_width(), 128);
    }

    #[test]
    fn test_create_bitfield() {
        let mut flags = Bitfield::new("Flags".to_string(), BackingType::U8);

        assert!(flags.add_field("readable".to_string(), 1).is_ok());
        assert!(flags.add_field("writable".to_string(), 1).is_ok());
        assert!(flags.add_field("executable".to_string(), 1).is_ok());
        assert!(flags.add_field("_reserved".to_string(), 5).is_ok());

        assert_eq!(flags.total_bits(), 8);
        assert_eq!(flags.remaining_bits(), 0);
        assert!(flags.is_complete());
        assert!(flags.validate().is_ok());
    }

    #[test]
    fn test_bitfield_overflow() {
        let mut flags = Bitfield::new("Flags".to_string(), BackingType::U8);

        assert!(flags.add_field("field1".to_string(), 4).is_ok());
        assert!(flags.add_field("field2".to_string(), 4).is_ok());
        // This should fail - only 8 bits available
        assert!(flags.add_field("field3".to_string(), 1).is_err());
    }

    #[test]
    fn test_bitfield_field_mask() {
        let field = BitfieldField::new("mode".to_string(), 1, 2);
        // Bits 1-2 should be set: 0b110 = 6
        assert_eq!(field.mask(), 0b110);
    }

    #[test]
    fn test_bitfield_extract_insert() {
        let field = BitfieldField::new("mode".to_string(), 1, 2);

        // Insert value 0b11 (3) at bits 1-2
        let backing = field.insert(0, 0b11);
        assert_eq!(backing, 0b110);

        // Extract value
        assert_eq!(field.extract(backing), 0b11);

        // Modify value
        let backing2 = field.insert(backing, 0b01);
        assert_eq!(backing2, 0b010);
        assert_eq!(field.extract(backing2), 0b01);
    }

    #[test]
    fn test_complex_bitfield() {
        let mut status = Bitfield::new("StatusReg".to_string(), BackingType::U32);

        assert!(status.add_field("enabled".to_string(), 1).is_ok());
        assert!(status.add_field("mode".to_string(), 2).is_ok());
        assert!(status.add_field("priority".to_string(), 4).is_ok());
        assert!(status.add_field("_reserved".to_string(), 25).is_ok());

        assert_eq!(status.total_bits(), 32);
        assert!(status.is_complete());
        assert!(status.validate().is_ok());

        let enabled = status.get_field("enabled").unwrap();
        assert_eq!(enabled.offset, 0);
        assert_eq!(enabled.width, 1);

        let mode = status.get_field("mode").unwrap();
        assert_eq!(mode.offset, 1);
        assert_eq!(mode.width, 2);

        let priority = status.get_field("priority").unwrap();
        assert_eq!(priority.offset, 3);
        assert_eq!(priority.width, 4);
    }

    #[test]
    fn test_field_fits() {
        let field = BitfieldField::new("value".to_string(), 0, 4);

        assert!(field.fits(0));
        assert!(field.fits(15)); // 0b1111
        assert!(!field.fits(16)); // 0b10000
        assert!(!field.fits(100));
    }
}
