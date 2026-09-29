# Bootstrap Centralized Storage Roots

The compiler/bootstrap producer projection places reusable authenticated caches
below `SIMPLE_USER_STORAGE_ROOT/cache` and stage, build, test, temporary, and
evidence artifacts below `SIMPLE_WORKTREE_STORAGE_ROOT`.

Explicit legacy output overrides remain supported and are identified as
`legacy-explicit-override` in the atomic storage-authority receipt. Storage
projection does not select a compiler, weaken admission, bypass provenance, or
introduce a Rust-seed fallback.

Ordinary native builds use the same user-scoped compiler cache authority, so
bootstrap and direct compilation can reuse authenticated objects without
placing mutable cache state in the source tree.
