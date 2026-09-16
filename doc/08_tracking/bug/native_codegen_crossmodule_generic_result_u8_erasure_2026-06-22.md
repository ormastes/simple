# Native AOT: cross-module generic `Result<[u8], E>` payload type erasure

## Triage 2026-09-13 — STILL OPEN: native AOT could not be exercised on this host
- **measured** — a probe was built (module `modB.spl` returning `Result<[u8], Err>`; the
  importer does `match get_bytes(3): case Ok(d) => print(d.len()); print(d[0])`). It prints
  `3` then `65` under `bin/simple run` — but the entry says the interpreter is unaffected,
  so that proves nothing.
- **measured** — the AOT lane does not work here at all:
  `bin/simple native-build <probe> -o <exe>` fails with
  `error: semantic: unknown extern function: rt_env_vars` /
  `native-build worker exited with code 1`, and a `--compile` invocation produced no
  artifact next to the source, so its identical `3` / `65` output cannot be attributed to
  native AOT.
- **inferred** — this AOT-only bug is neither confirmed nor cleared from this Windows seed
  host. Left OPEN. (An earlier draft of this triage closed it on the `--compile` output;
  that was withdrawn once the missing artifact and the native-build failure were seen.)

**Status:** OPEN — see the Triage 2026-09-13 section below
**Date:** 2026-06-22 (supersedes the 2026-06-21 doc dropped by parallel churn).
**Mode:** native AOT only (`bin/simple <file> --compile` / `native-build`). Interpreter and `check` are unaffected.

## Symptom
A `[u8]` payload extracted from a cross-module generic `Result<[u8], E>` via
`match ...: case Ok(d) => ... d[0] ...` loses its static `[u8]` element type.
`d.len()` works; **indexing** `d[0]` lowers to the dynamic `rt_index_get` path,
hits an unlinked post-index convert, and faults (`call *[NULL]`). Compilation-
unit-dependent: minimal repros pass; reproduces only in a generics-heavy unit
(e.g. the real `StdFsNvfsClient`). `var d2: [u8] = d` re-types the leaf and
works — an explicit annotation, not inference.

## CORRECTED root cause (the 2026-06-21 hypothesis was wrong)
The earlier doc blamed the type checker's `extract_pattern_bindings`
(`30.types/type_system/bidirectional.spl:405`). That function is **dead code**:
it references an out-of-scope `engine` (no such parameter) and is never reached
from the native pipeline. `bidirectional.spl` is an unused/experimental checker.

The real chain:
1. **Native `--compile` runs a no-op type checker.**
   `src/compiler/00.common/compiler_services.spl` — `create_default_services()`
   wires `_make_noop_type_checker()` (`_noop_check` returns `[]`). No type
   inference runs before MIR lowering, so no expression carries a resolved
   instantiated generic type.
2. **HIR lowering never stamps the payload type.**
   `src/compiler/20.hir/hir_lowering/expressions.spl:505` hardcodes
   `type_: nil` for *every* `HirPattern`. The `Enum` case (lines 465–483) looks
   up the enum symbol with **empty type args** (`Named(symbol, [])`) and lowers
   payload sub-patterns with no type — the variant's payload type is never
   extracted from the instantiated `Result<[u8], E>`.
3. **MIR index lowering defaults to dynamic.**
   `src/compiler/50.mir/mir_lowering_expr_part1.spl:225` reads `expr.type_`,
   finds nil, defaults the element type → `local_is_array` is false
   (`60.mir_opt/mir_opt/collection_opt_core.spl:368`) → dynamic `rt_index_get`
   path → unlinked convert → fault.

## Why this is NOT a contained fix
Recovering `[u8]` at HIR-lowering time needs the match subject's *instantiated*
generic type (`Result<[u8], E>`). With the no-op checker, that type exists
nowhere by HIR time. A real fix requires either (a) real generic type
propagation through the native pipeline, or (b) switching native `--compile` to
a real type checker **and** fixing variant-payload extraction there
(`30.types/type_system/stmt_check_part1.spl:365` `EnumPattern` also assigns the
whole subject type, not the payload). Both are major compiler subsystems —
disproportionate to the payoff (un-gating two svllm byte tests).

## 2026-07-15 resolution

The imported function symbol already retains its concrete
`Result<[u8], E>` return type through HIR and the no-op monomorphization pass.
The remaining erasure was contained to MIR enum-pattern binding:
`rt_enum_payload` necessarily returns an `i64` word, but the bound local lost
the existing runtime-array marker. `lower_enum_match` now recovers the selected
`Ok`/`Err` payload type from the scrutinee signature and preserves that marker
for Array/Slice payloads, routing `data[i]` through `rt_array_get`.

`scripts/check/check-native-crossmodule-result-u8.shs` builds the focused
cross-module fixture with both LLVM and Cranelift under
`SIMPLE_NO_STUB_FALLBACK=1` and checks exact execution output. The checker was
added but not executed in this source-only lane; bootstrap/build/deploy was
explicitly out of scope.

## Historical mitigation

Production svllm previously avoided the erased leaf with typed `[[u8]]`
containers and gated byte-value tests behind `native_u8_fixed`. Those named
gates are no longer present in the current tree; the focused dual-backend
checker above is their replacement regression.

## Deploy note for whoever takes the real fix
`bin/simple build bootstrap` only determinism-checks the 30 KB `bootstrap_main`
entry — it does **not** rebuild the real compiler. The full self-hosted compiler
is built by `scripts/bootstrap/bootstrap-from-scratch.sh` (Rust seed → stage2
`native-build --source src/compiler --source src/app --source src/lib
--entry-closure`). Stage2 yields a deployable binary; stage3 self-host
convergence is the historically-fragile part.
