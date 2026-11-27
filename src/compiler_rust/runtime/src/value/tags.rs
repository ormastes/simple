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
pub const SPECIAL_ERROR: u64 = 3;
// Symbol IDs start at 4

// Char values (ADR-005): a TAG_SPECIAL sub-kind disjoint from symbol IDs.
// payload = SPECIAL_CHAR_BASE | code_point. Symbol IDs are small counters and
// never reach bit 40, so the ranges cannot collide. Never TAG_INT: a char must
// not compare equal to its code point or print as a number.
pub const SPECIAL_CHAR_BASE: u64 = 1 << 40;
pub const SPECIAL_CHAR_MASK: u64 = 0x1F_FFFF;
