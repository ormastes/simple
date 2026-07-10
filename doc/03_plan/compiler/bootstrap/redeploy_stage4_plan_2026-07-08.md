# Stage4 Self-Host Redeploy (#79) — Plan (updated 2026-07-10)

> Full dated archaeology of the fix arc (SIGSEGV → DataLayout → verifier
> errors → object emission) moved to
> `redeploy_stage4_plan_history_2026-07.md`. This file is the current status
> and the forward plan only.

## Goal

`bin/simple build bootstrap` (or the equivalent stage2 self-compile) produces a
working self-hosted `simple` binary from current `src/`, gateable and
redeployable to `bin/release/<triple>/simple`.

## STATUS NOW (as of origin `06facdc1`)

Stage 1 of `bin/simple build bootstrap` runs the **llvm-lib AOT / LLVM-C-API**
path (`src/compiler/70.backend/backend/llvm_lib_*`, native-build LLVM-IR
generation run **interpreted** by the deployed `bin/simple`). As of
`06facdc1`:

- **All crash classes are eliminated.** No SIGSEGV, no SIGABRT, no dropped
  calls, no verifier errors. IR generation, verification, and object emission
  all succeed — `object.app.cli.bootstrap_main.o` is written as a valid
  `Mach-O 64-bit object arm64` on this host.
- **Current wall (in-flight, a parallel agent is fixing it now):** a frontend
  **semantic** error, not codegen:
  ```
  error: semantic: method 'replace' not found on value of type str in nested call context
  error: native-build worker exited with code 1.
  ```
  This is `str.replace` resolution failing in a nested call context — unrelated
  to the llvm-lib backend fix arc that got here. Do not re-diagnose the
  codegen/emission path for this; it's a separate, later-stage bug.
- Deployed `bin/simple` (unchanged) still works as a tool in the meantime.

## WHAT LANDED (fix arc, oldest → newest, all on origin/main)

| Commit | One-liner |
|---|---|
| `bfd98b03` (#130) | Stop wiping call/method args under `SIMPLE_BOOTSTRAP` — first ICmp SIGSEGV instance fixed, wall moved to a DataLayout abort (134). |
| `d16a8883` (#133) | Lower function params under `SIMPLE_BOOTSTRAP` — DataLayout wall fixed, wall moved back to exit 139 (ICmp SIGSEGV, different site). |
| `9d11e852` | Declare `rt_cli_get_args` extern (real fix for a dropped call, but crash-report comparison proved it was independent of the fatal 139 — wall re-diagnosed). |
| `9bea509a` | Eliminate use-before-def MIR locals (`lower_if`/`lower_method_call` merge placeholders) + map builtin `print`→`rt_println` — **Stage-1 SIGSEGV (139) eliminated**, now a clean error (exit 1). |
| `f3fb1ed3` | Print LLVM verifier's specific failures on refuse-to-emit + i64 placeholder temps — itemized the Stage-1 wall into a concrete list (19 verifier errors, 6 classes). |
| `2c15339a` | Array→ptr type mapping fix (dominant verifier-error class), correct LLVM kind constants, ret/binop coercion, null-operand diagnostics — verifier errors 19→1. |
| `2f396589` | Match/switch merge-placeholder gap (same class as `9bea509a`'s `lower_if` fix, missed in `lower_match`) + null-guards on remaining translator paths (If-cond, call_indirect/intrinsic args). |
| `ff834dab` | NUL-terminate `LLVMBuildCall2`'s `Name` arg — empty `text.ptr()` is a dangling sentinel in this runtime, was segfaulting `strlen` inside LLVM's C API. **Stage-1 SIGSEGV eliminated for good.** |
| `d80fdadd` | `Ret` with an unmapped operand was building a zero-operand `ReturnInst` (silent verifier mismatch) — now synthesizes a typed placeholder + names the diagnostic. **Verifier now clean.** Wall moved to object emission. |
| `06facdc1` | Triple-aware `Host` CPU selection (was hardcoding `x86-64` for `Host` even on aarch64 — LLVM rejected it and fell back to a garbage subtarget) + format-aware object-magic check (was ELF-only, rejected valid Mach-O). **Object emission SUCCEEDS** (valid Mach-O arm64). Wall moves to the current semantic `replace` error. |

Full per-fix diagnostic detail (probes, crash reports, budget accounting):
`doc/08_tracking/bug/bootstrap_stage1_native_build_llvm_icmp_segfault_2026-07-09.md`.

## NEXT STEPS (in order)

1. **Semantic wall (in-flight — a parallel agent owns this right now, do not
   duplicate work):** `method 'replace' not found on value of type str in
   nested call context`. Locate the `str.replace` call resolution gap in the
   frontend (nested-call-context method resolution) and fix it in
   `.spl` source — this is not a backend/emission issue.
2. **Whatever wall follows**, per the bug doc's continuation once (1) lands —
   check the bug doc's latest section before starting new diagnosis to avoid
   re-treading ground.
3. **Reconcile the two emit paths.** The original plan (2026-07-08) framed
   path 2 (llvm-lib AOT) as "long-horizon" and path 1 (cranelift/llc
   `SIMPLE_BOOTSTRAP`) as "the realistic route." That framing is now stale:
   path 2 is the path `bin/simple build bootstrap`'s Stage 1 actually runs,
   and it has advanced all the way through IR-gen, verification, and object
   emission to a late-stage semantic error. Path 1's string-literal-drop
   investigation (preserved in the history appendix) is now the
   deprioritized path — do not resume it unless path 2 hits a dead end.
4. **Re-gate + redeploy criteria.** Once Stage 1 (path 2) passes end-to-end:
   run the full `bin/simple build bootstrap` 3-stage (not just Stage 1 in
   isolation) and the extended smoke matrix before any redeploy to
   `bin/release/<triple>/simple`. Do not redeploy on a Stage-1-only pass.

## STANDING TRAPS

- **Peer WC-sweeps re-reverting fixes.** A concurrent full-WC sync from
  another session can silently revert uncommitted edits within seconds.
  Re-verify these sentry sites after any sync or `workspace update-stale`
  before trusting the tree:
  - `llvm_lib_translate_expr.spl:504` / `:506` — `get_value(value_map,
    local.id)` (not raw `local`).
  - All 3 `llvm_types.spl` copies — `LLVMSetDataLayout`'s `layout` arg via
    `(layout + "\0").ptr()`.
  - All 4 `LLVMBuildCall2` call sites — `Name` arg via `(name + "\0")`.
  - `llvm_lib_translate.spl`'s 3 named `Ret`-case diagnostics/placeholders.
  - `llvm_target.spl`'s `for_target_portable_numeric_with_mode` — `Host` has
    its own arm calling `detect_host_arch()`, not grouped with `X86_64`.
- **Stale-WC backup drill.** Before running `jj workspace update-stale` (or
  any operation that can discard uncommitted edits), back up edited files to
  the scratchpad first, then re-verify content after.
- **ONE bootstrap at a time.** `pgrep` for a concurrent `native-build`/`build
  bootstrap` before starting a diagnostic run — each run takes ~400s and two
  overlapping runs corrupt each other's evidence.
- **Duplicate module files.** Numbered (`50.mir`, `70.backend`) vs
  non-numbered (`mir`, `backend`) directories both exist; the seed resolves
  an import to one copy, and instrumentation on the other silently never
  fires. Same for `nogc_sync_mut` vs `nogc_async_mut` `sffi`/`ffi` copies —
  `use std.sffi.llvm.*` resolves to the `nogc_async_mut` copy first
  (resolver order), so `nogc_sync_mut/sffi` is a dead copy for that import
  path. Verify which copy is live before trusting a probe's silence.
- **`(s + "\0").ptr()` rule for C strings.** This runtime's `text.ptr()` on
  an empty or non-NUL-terminated string can return a dangling/non-strlen-safe
  pointer. Any text handed to an LLVM C API (or other extern) that internally
  `strlen`s it must be NUL-terminated explicitly via `(s + "\0").ptr()` —
  this was the root cause of two separate SIGSEGVs in this arc
  (`LLVMSetDataLayout`, `LLVMBuildCall2`).

## Reference

- Bug doc (full diagnostic history, crash reports, budget accounting):
  `doc/08_tracking/bug/bootstrap_stage1_native_build_llvm_icmp_segfault_2026-07-09.md`
- Historical dated sections from this plan (verbatim, oldest → newest):
  `redeploy_stage4_plan_history_2026-07.md`
