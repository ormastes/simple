# memory_types_spec

*Source: `simple/std_lib/test/features/types/memory_types_spec.spl`*

---

Memory Types - Feature #18

Overview:
    Reference capability system with GC-managed references (T), unique pointers (&T),
    shared pointers (*T), weak pointers (-T), and handle pointers (+T). Provides
    flexible memory management strategies with GC as the default and manual memory
    management as opt-in.

Syntax:
    T      - GC-managed reference (default, most code)
    &T     - Unique pointer (single owner, RAII)
    *T     - Shared pointer (reference counted)
    -T     - Weak pointer (non-owning, breaks cycles)
    +T     - Handle pointer (slot + generation, pool-managed)

Implementation:
    - GC references are heap-allocated and automatically managed
    - Unique pointers transfer ownership on assignment/call
    - Shared pointers maintain reference counts
    - Weak pointers can be upgraded to strong references
    - Handle pointers use slot/generation validation
    - Mutability tracked via mut keyword

Notes:
    - GC is default for ease of use
    - Manual memory is opt-in via pointer types
    - RAII for unique pointers
    - Reference counting for shared pointers
