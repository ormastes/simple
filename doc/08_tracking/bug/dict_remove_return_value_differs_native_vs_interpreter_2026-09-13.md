# `Dict.remove(k)` returns a new dict interpreted but the removed VALUE natively
## Open 2026-09-16 — needs owner triage

Reviewed in the 2026-09-16 bug-ledger normalization pass; no resolution
evidence found in the body. This is bookkeeping, not verification.

**Filed:** 2026-09-13
**Lane:** seed interpreter vs seed native codegen (LLVM and Cranelift lanes alike)
**Severity:** silent state corruption in any code spelled `d = d.remove(k)` — this
is what broke phase-2 `str(i64)` (see
`phase2_str_returns_raw_pointer_2026-09-13.md`).

## Symptom

`self.marks = self.marks.remove(id)` on a `Dict<i64, bool>` class field:

| lane | `d.remove(k)` returns | effect of `d = d.remove(k)` |
|---|---|---|
| interpreter (`interpreter_method/collections.rs` `"remove" \| "delete"`) | a NEW dict without `k`; original untouched | correct |
| native (`codegen/instr/closures_structs.rs:2293`, `codegen/llvm/functions.rs:2920` → `rt_collection_remove` → `value/dict.rs:363 rt_dict_remove`) | the REMOVED VALUE, or nil | the field now holds `true`/nil; every later `.contains`/`[k] = v` on it is a no-op or a miss |

A bare `d.remove(k)` statement is the mirror-image bug (mutates in place
natively, no-op interpreted). No single spelling of `remove` is correct on both
lanes.

## Measured consequence (phase 2, natively compiled Stage 2)

`mir_lowering_stmts.spl` unmarked per-local marker maps
(`tagged_text_locals`, `option_value_locals`, `runtime_array_locals`,
`runtime_dict_locals`, `nil_locals`, `array_element_struct_syms`) with exactly
that idiom on every plain assignment. After the first `t = t + 1` in a function
the maps were clobbered, `is_tagged_text_local` missed, and `"A=" + str(t)`
rendered the result of `rt_raw_i64_to_string` a SECOND time through
`coerce_concat_operand` — printing the tagged string handle
(`2083130940001`) instead of `3`. Disassembly of the phase-2 object showed two
`rt_raw_i64_to_string` calls with `mov rcx,rax` between them.

## Fix applied (workaround, in the compiler)

`marker_map_without` / `text_map_without` in `mir_lowering_types.spl` rebuild the
map without the key (guarded by `contains_key` so the common case stays O(1));
all 10 sites in `mir_lowering_stmts.spl` use them. Probe
(`build/p2run/dictprobe/marker_smoke.spl`) verified under the interpreter.

## Still open (the language defect)

- Decide the contract for `Dict.remove` (return the dict? the value? mutate?)
  and make interpreter, `rt_dict_remove`, and both native lowerings agree.
- ~40 further `self.x = self.x.remove(k)` sites remain in
  `src/compiler/99.loader/**`, `40.mono/monomorphize/cache.spl`,
  `15.blocks/blocks/registry.spl`, `20.hir/.../trait_impl_lowering.spl`
  (`git grep -n "= self\.[a-z_]*\.remove("`). They are equally wrong natively.
- The `core-c-bootstrap` runtime's `rt_collection_remove` is a named TRAP stub
  (`c_runtime_missing_83_codegen_runtime_symbols_2026-08-21.md`); phase 2 only
  survived because its link resolved the Rust implementation.

