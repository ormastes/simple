# Retired bootstrap spec examples: LLVM bootstrap receiver and file-move ABI

- **Filed:** 2026-09-26
- **Status:** open — re-land the feature, then restore the retired examples
- **Component:** `src/compiler/70.backend/backend/_MirToLlvm/`, `src/compiler/80.driver/driver_bootstrap.spl`, `src/runtime/runtime*.c`, SFFI generator specs

## Why these were retired

These examples arrived through the share-history squash `e274cd33719`
(2026-08-27). Main does not have the behaviour they pin. The remaining examples
in both files were retargeted to main with cited commits and pass under the seed.
Owner decision 2026-09-26: retire and track.

## Missing features

| Spec (test/01_unit/compiler/bootstrap/) | Retired example | Missing on main | Origin commit |
|---|---|---|---|
| `bootstrap_flat_llvm_receiver_ownership_spec.spl` | "keeps static and function emission on one receiver" | `bootstrap_emit_real_llvm_object` still builds a fresh translator (`MirToLlvm.create` + `register_bootstrap_signatures`) instead of emitting statics and functions on one staged receiver | `a8244005f9b` (pre-squash copy of the merge) |
| same | "does not retain mutable static or string collections on the staged receiver" | `emit_bootstrap_statics` still keeps `var emitted_names: Dict<text, bool>` on the receiver | `a8244005f9b` |
| same | "attributes rejected call conversions to their exact owner" | "unsupported LLVM value conversion" panics carry no `function=` / `value=` attribution | `a8244005f9b` |
| `file_rename_move_abi_contract_spec.spl` | "keeps generated bindings and native fallback honest" | Both SFFI generator specs still declare `rt_file_rename` with `return_type: "void"`, and `native_binary/stubs.rs` registers a no-op 2-arg `rt_file_rename` | `19b686ee050` (2026-08-10, fix(runtime): make cross-device moves failure-atomic) |
| same | "publishes cross-device moves without deleting caller destinations" | Neither `runtime.c` nor `runtime_native.c` publishes an EXDEV move through a temp file followed by `rename` | `19b686ee050` |
| same | `rt_file_rename` and lib-translate parts of "keeps both LLVM lanes on the four-word text ABI" | `llvm_backend.spl` declares no four-word `rt_file_rename`; the LLVM C-API lane `llvm_lib_translate.spl` no longer exists | `19b686ee050` |

Related open bug: `doc/08_tracking/bug/rt_file_rename_move_abi_lanes_drifted_2026-09-06.md`.

## Re-land checklist

1. Land the feature on main.
2. Restore the example from its origin commit, escaping literal `{` in needles
   as `\{`.
3. Run it under the seed and the self-hosted CLI; it must pass on both.
