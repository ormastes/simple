# rt_ Mapping and Pointer Contract Plan

Design: doc/05_design/compiler/rt_mapping_pointer_contract_design.md

| Stage | Scope | Status |
|---|---|---|
| R0 | Baselines and negative fixtures | Partial: pointer-return guard, #5648 |
| R1 | Canonical contract records and profile view | Partial: metadata index only, `scripts/check/rt-binding-index.py` (one record per extern, stable interface id, per-host provider rows, map and pointer verdicts, compile and link UNTESTED). Not done: SDN contract records, profile view, and any compile or link evidence |
| R2 | Compiler-generated mapping and pointer evidence, both directions | Partial, C side only: `scripts/check/check-rt-c-contract-compile.py` compiles each scanned extern prototype into a TU with `cc -fsyntax-only` (per-symbol PASS/FAIL/UNTESTED, current host only, run on demand, not in CI). Default TUs: runtime_simd_dispatch.c and the other runtime_nonnull.h includers. Apple clang 17, arm64: dispatch 28 PASS / 0 FAIL / 41 UNTESTED; default set 68 PASS / 8 FAIL / 551 UNTESTED (627 rows). All 551 UNTESTED rows are unmapped `.spl` types (`text`, arrays, optionals, Vec*). The 8 FAILs are declaration disagreements the TU sees: return type only in 3 (rt_mem_snapshot_close and rt_process_owned_v3_release_value, `.spl` bool vs C int; rt_is_macro_trace_enabled, no `.spl` return type indexed void vs C bool); parameter ABI in 5 rt_file_* rows (`.spl` raw i64 for pointer and length vs runtime.h's pointer and uint64 text ABI). Not done: Simple-side compile, `text`/array/optional/class parameter types, link, other hosts, CI wiring |
| R3 | End-of-build all-variant audit | Not started |
| R4 | Warn-to-error migration | Started: shrink the 38-row return baseline |
| R5 | Retire overlapping scanners and lists | Not started |

Current gate: scripts/check/check-rt-pointer-ref-map.py. At #5648: 270 edges, 38 baselined, 138 UNKNOWN.
Text scan only. Compile and link are UNTESTED on every host; parameters are not yet checked.

Migration blocker: the interpreter keeps `T?` wrapped in typed bindings, fields, `.push` and `for`.
Each signature change must update its call sites and carry a RED-to-GREEN spec.
