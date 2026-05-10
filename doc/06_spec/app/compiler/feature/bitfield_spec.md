# Bitfield Specification

**Feature ID:** #BM-004 | **Category:** Language / Bare-Metal | **Status:** In Progress

_Source: `test/feature/usage/bitfield_spec.spl`_

---

Bitfields allow packing multiple values into a single integer:
- Efficient hardware register access
- Network protocol fields
- Compact data structures

Syntax:

Features:
- Automatic offset calculation
- Compile-time overflow checking
- Generated getters/setters
- Enum support (bits inferred)

---

## Test Summary

| Metric | Count |
|--------|-------|
| Tests | 22 |

## Test Structure

### Bitfield Definition
_Defining bitfield types._

#### Basic Bitfields
_Simple bitfield definitions._

- ✅ defines bitfield with u8 backing
- ✅ defines bitfield with u16 backing
- ✅ defines bitfield with u32 backing
- ✅ defines bitfield with u64 backing
#### Bit Width Types
_Using different bit width types._

- ✅ supports arbitrary unsigned widths
- ✅ supports arbitrary signed widths
#### Reserved Fields
_Using _ for reserved/padding bits._

- ✅ allows reserved fields
- ✅ allows multiple reserved fields
### Bitfield Operations
_Getting and setting bitfield values._

#### Getters
_Reading bitfield values._

- ✅ reads single bit
- ✅ reads multi-bit field
- ✅ reads signed fields correctly
#### Setters
_Writing bitfield values._

- ✅ sets single bit
- ✅ sets multi-bit field
- ✅ preserves other fields when setting
#### Raw Value Access
_Accessing the raw backing value._

- ✅ gets raw value
- ✅ sets raw value
### Bitfield Validation
_Compile-time validation._

#### Overflow Detection
_Detecting bit overflow._

- ✅ validates total bits fit in backing
- ✅ validates large bitfields
### Use Cases - Hardware Registers
_Real-world bitfield examples._

#### x86 Control Registers
_x86 CPU control register layouts._

- ✅ models CR0 register
- ✅ models EFLAGS register
#### Page Table Entry
_x86 page table entry format._

- ✅ models 32-bit page table entry
#### Network Headers
_Network protocol bitfields._

- ✅ models TCP flags

