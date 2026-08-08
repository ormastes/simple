# Interpreter Shared Text — TLDR

Replace Rust interpreter `Value::Str(String)` with immutable
`Value::Str(Arc<String>)`. Object COW then clones field maps while sharing large
lexer source buffers. No parallel variant, interning, ABI, or wire-format change.

Migrate alias/constructor/tests first, then the variant, shared-Arc constructor,
and all compile fixes coherently.
Text transformations always allocate new shared text; existing Arcs clone
directly. Gate on exact string/Unicode/bridge semantics, executor pointer
identity, an Arc-mutation source guard, two reproducible max-RSS baselines
(parser and many-distinct-short-text) <=10%, and 22 KiB parsing under 15s before
bootstrap.

Inspect: `value.rs`, `value_pointers.rs`, `value_impl.rs`, `node_exec.rs`,
`runtime_bridge.rs`, `value_bridge.rs`.
