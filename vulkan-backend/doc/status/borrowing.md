# Feature #29: Borrowing

**Status**: Implemented (Runtime Borrow Checking)
**Difficulty**: 5 (original - hardest feature)
**Importance**: 4

## Summary

Borrowing provides memory safety through references. Currently implements runtime borrow checking via `RwLock`, with the foundation laid for future compile-time checking.

## Implemented Syntax

```simple
# Immutable borrow with & operator
let x = 42
let y = &x      # immutable borrow
let val = *y    # dereference

# Mutable borrow with &mut operator
let a = 10
let b = &mut a  # mutable borrow
let val2 = *b   # dereference

# Multiple immutable borrows allowed
let p = &x
let q = &x
let sum = *p + *q

# Pass borrows to functions
fn read_ref(r):
    return *r

let borrowed = &x
let result = read_ref(borrowed)

# Nested borrows
let ref1 = &x
let ref2 = &ref1
let inner = *ref2
let val = *inner
```

## Features Implemented

**Phase 1 - Syntax + AST:**
- [x] `&expr` immutable borrow expression (UnaryOp::Ref)
- [x] `&mut expr` mutable borrow expression (UnaryOp::RefMut)
- [x] `PointerKind::Borrow` and `PointerKind::BorrowMut` in AST
- [x] `Value::Borrow` and `Value::BorrowMut` runtime representations
- [x] Thread-safe borrow values using `Arc<RwLock<Value>>`
- [x] Dereference support for borrows via `*` operator
- [x] Basic interpreter evaluation of borrow expressions

**Phase 2 - Type System:**
- [x] `Type::Borrow(Box<Type>)` and `Type::BorrowMut(Box<Type>)` in type checker
- [x] Type unification for borrow types
- [x] Subtyping: `&mut T` can be used where `&T` is expected
- [x] Type inference for `&`, `&mut`, and `*` operators
- [x] AST pointer type to type checker type conversion

**Phase 3 & 4 - Runtime Borrow Checking:**
- [x] Runtime aliasing enforcement via `RwLock`
- [x] Multiple immutable borrows allowed simultaneously (via `read()`)
- [x] Single mutable borrow at a time (via `write()`)
- [x] Panic on borrow violations (attempting mutable borrow while immutable exists)

## Future Enhancements

- [ ] Compile-time borrow checker (static analysis)
- [ ] Lifetime annotations and inference
- [ ] Borrow scope tracking across function boundaries
- [ ] Better error messages for borrow violations

## Why Difficulty Remains 5

This is the most complex remaining feature:
- Requires full borrow checker from scratch
- Lifetime analysis is notoriously difficult
- Must integrate with all existing pointer types
- Error messages must be clear and helpful
- No existing infrastructure to build on
- Rust took years to get borrow checking right

## Dependencies

- Requires significant type system work
- Needs lifetime annotations or inference
- Complex semantic analysis pass

## Complexity

Requires:
- New compiler pass for borrow checking
- Lifetime region inference
- Error reporting for violations
- Integration with Unique/Shared/Weak/Handle pointers

## Alternative Approach

Consider deferring full borrowing and using:
- Runtime borrow checking (like RefCell)
- Simpler ownership model
- Escape hatch with `unsafe` blocks

## Related

- #25 Unique Pointers (implemented)
- #26 Shared Pointers (implemented)

## Split Into Smaller Deliverables

Phase the feature so we can land value without a full borrow checker on day one:

1) **Syntax + AST plumbing**  
   - Parse `&T_borrow`/`&mut T_borrow` in types and patterns.  
   - Represent borrows as distinct variants in the type AST and `type` crate without enforcing rules yet.

2) **Type surface + inference hygiene**  
   - Extend type inference to carry borrow qualifiers; ensure functions, struct fields, and locals can be typed as borrow references.  
   - Emit simple diagnostics for forbidden upcasts (e.g., `&mut T_borrow` → `&T_borrow` allowed, but not vice versa).

3) **Local aliasing checks (function body only)**  
   - Introduce a lightweight dataflow pass over a lowered MIR/CFG that enforces: multiple immutable borrows OR one mutable borrow per local binding; no mutable + immutable overlap.  
   - Scope limited to locals and block scope; no closures or captured borrows yet.

4) **Region inference with block scopes**  
   - Track basic lifetimes per binding/borrow at block granularity to reject escapes (returning a borrow to a dead local, storing into longer-lived struct fields).  
   - Still no closure captures; keep regions intra-function.

5) **Captured borrows + structs/actors**  
   - Allow storing borrows in struct fields and capturing them in closures/actors with region checks that include capture environments.  
   - Add diagnostics for self-referential captures and cross-actor leaks.

6) **Runtime escape hatch (optional, gated)**  
   - Provide a `checked_borrow` builtin backed by runtime guards (RefCell-like) for parts of the language not yet covered by static analysis.  
   - Mark its use as `unsafe`/unstable to keep static borrow checking the default path.

## Current Blockers

- Type checker lacks lifetime/region representation; needs a place to attach borrow qualifiers.  
- No MIR/CFG layer to run alias analysis—must be introduced or reuse compiler lowering.  
- Diagnostics pipeline for semantic passes is minimal; borrow errors will require structured spans/labels.
