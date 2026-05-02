# borrowing_spec

**Category:** Memory Management | **Status:** In Progress

_Source: `test/feature/usage/borrowing_spec.spl`_

---

Reference Capabilities and Borrowing Specification


Tests for the borrowing system including mutable (mut T), isolated (iso T),
and immutable reference capabilities. Verifies proper ownership transfer,
mutable access restrictions, and isolation guarantees.

---

## Test Summary

| Metric | Count |
|--------|-------|
| Tests | 4 |

## Test Structure

### Borrowing and Reference Capabilities

#### Immutable references

- ✅ allows multiple immutable borrows
#### Mutable references

- ✅ prevents simultaneous immutable and mutable borrows
#### Isolated references

- ✅ ensures exclusive access to isolated values
#### Ownership transfer

- ✅ transfers ownership correctly through function calls

