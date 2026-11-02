# Typed array methods box Bool values as integers

Status: OPEN (P1) — source-level owner and representation mismatch identified; no native reproduction or production fix claimed.

## Static owner finding

In `src/compiler_rust/compiler/src/mir/lower/lowering_expr_method.rs`,
`MirLowerer::lower_method_call` has array-receiver paths for `.push` and
`.index_of`. Both `needs_push_boxing` / needle boxing predicates include
`TypeId::BOOL`, and their fallback emits `MirInst::BoxInt`. That represents
Bool values as tagged integers before the runtime array method uses them.

The collection literal path in
`src/compiler_rust/compiler/src/mir/lower/lowering_expr_collection.rs` instead
uses `rt_value_bool` for Bool elements. This makes the method path inconsistent
with the array literal representation: `.push(true)` may store a different
tag, and `.index_of(true)` may search using a different tag. This is a static
representation analysis, not an executed regression; no native result is
claimed.

Keep this array-method issue separate from the fixed multi-field enum
constructor path and the OPEN single-field enum constructor finding. A focused
native test should cover Bool `.push` and `.index_of` with both true and false,
plus controls using Bool array literals and numeric values.
