# borrowing_spec

*Source: `simple/std_lib/test/features/types/borrowing_spec.spl`*

---

Borrowing - Feature #19

Overview:
    Ownership semantics with move, borrow, and lifetime tracking. Ensures memory
    safety without garbage collection for manual memory types. Each value has
    exactly one owner, and ownership can be transferred or temporarily borrowed.

Syntax:
    val x = Resource { ... }     # x owns the resource
    val y = x                    # ownership transferred (move)
    fn process(r: Resource)      # takes ownership
    fn read(r: Resource)         # immutable borrow (implicit)

Implementation:
    - Single ownership: each value has one owner
    - Move semantics: assignment transfers ownership
    - Immutable borrows: multiple readers allowed
    - Mutable borrows: exclusive write access
    - Lifetime tracking: prevents dangling pointers
    - Copy semantics for primitives (i64, bool, etc.)
    - Compile-time checking for safety

Notes:
    - Move transfers ownership
    - Borrow creates temporary reference
    - Lifetimes prevent dangling pointers
    - Checked at compile time
