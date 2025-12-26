//! Tag bits for the tagged pointer representation.

pub const TAG_MASK: u64 = 0b111;
pub const TAG_INT: u64 = 0b000;
pub const TAG_HEAP: u64 = 0b001;
pub const TAG_FLOAT: u64 = 0b010;
pub const TAG_SPECIAL: u64 = 0b011;

// Special value subtypes (encoded in payload)
pub const SPECIAL_NIL: u64 = 0;
pub const SPECIAL_TRUE: u64 = 1;
pub const SPECIAL_FALSE: u64 = 2;
// Symbol IDs start at 3
