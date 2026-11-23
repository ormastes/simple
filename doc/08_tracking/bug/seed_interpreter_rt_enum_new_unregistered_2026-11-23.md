# Seed interpreter has no `rt_enum_new` extern — 2026-11-23

Status: open; spec parked as `@tag:in-development` in
test/01_unit/compiler/hir/hir_codec_char_wire_nil_spec.spl.
Owner: src/compiler_rust/compiler/src/interpreter_extern (extern registry).

Decoding the HIR CharLit wire-nil marker (`4\n\\N\n`) goes through
`hc_restore_enum_nil` -> `enum_wire_restore_nil`
(src/lib/nogc_sync_mut/sffi/enum_wire.spl:114) -> `rt_enum_new<T>`. Under the
deployed Windows seed (`bin/simple.exe`, 2026-11-19 build) this fails with:

    semantic: unknown extern function: rt_enum_new

`rt_enum_new` is listed in common/src/runtime_symbols.rs and used by codegen,
but it is not inserted in the interpreter extern registry. This is the same
third-registry gap that `rt_heap_ref_registered` had (sffi_value.rs,
2026-10-19). Every enum-slot nil restore in the generated HIR codec therefore
fails under the seed interpreter.

Fix: add an interpreter adapter for `rt_enum_new` and redeploy the seed. Then
remove the in-development tag and fold the example back into
hir_codec_char_spec.spl.

Side observation, not yet triaged: under `simple run` (JIT lane),
`rt_heap_ref_registered` returned false for every user enum value while
`rt_heap_ref_wellformed` returned true. The generated encoder would reject
every enum node in that lane.
