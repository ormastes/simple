# Native AOT: cross-module generic `Result<[u8], E>` payload type erasure

**Status:** OPEN — blocked on a large prerequisite (not a contained fix).
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

## Current mitigation (in place, sufficient)
- Production svllm byte-load uses `match` destructuring (no `is_err`/`unwrap`)
  and typed `[[u8]]` containers; the heavy path lives in the gc tier
  (`gc_async_mut/svllm/nvfs_client/std_fs.spl`, no `is_err`/`unwrap`).
- The two byte-value tests stay gated behind `native_u8_fixed == 1`
  (`test/01_unit/lib/nogc_async_mut/svllm/nvfs_client/std_fs_transport_spec.spl`,
  `test/03_system/tools/svllm_fs_loader_system_spec.spl`). Honestly gated — not
  silently failing.

## Deploy note for whoever takes the real fix
`bin/simple build bootstrap` only determinism-checks the 30 KB `bootstrap_main`
entry — it does **not** rebuild the real compiler. The full self-hosted compiler
is built by `scripts/bootstrap/bootstrap-from-scratch.sh` (Rust seed → stage2
`native-build --source src/compiler --source src/app --source src/lib
--entry-closure`). Stage2 yields a deployable binary; stage3 self-host
convergence is the historically-fragile part.
