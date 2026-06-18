# Bootstrap Stage 3 self-host fails — stage2 `bootstrap_main` binary can only emit a seed-wrapper, not real native code

- **Id:** bootstrap_stage3_selfhost_seed_wrapper_fallback_2026-06-17
- **Status:** Open
- **Severity:** P2 (self-host verification is skipped on every full bootstrap;
  Stage 4 silently falls back to the Rust seed, so the produced
  `build/bootstrap/full/<triple>/simple` is never the self-hosted compiler. The
  reproducible-build guarantee — stage2 SHA256 == stage3 SHA256 — cannot be
  checked. Not a runtime-correctness bug; the seed-built artifacts are valid.)
- **Found:** 2026-06-17 (full-bootstrap regression verification for the JIT
  composite extern-return fix, commit `49ca9697987`; reproduced across two
  consecutive `scripts/bootstrap/bootstrap-from-scratch.sh` runs)
- **Component:** bootstrap pipeline / self-hosted native-build
  (`bootstrap_main.spl`, `native-build` lowering/codegen, cranelift backend)
- **Files:**
  - `scripts/bootstrap/bootstrap-from-scratch.sh` (Stage 3 driver + warning text)
  - `src/app/cli/bootstrap_main.spl` (minimal CLI entry used for stage2/stage3)
  - `build/bootstrap/logs/<triple>/stage3-native-build.log`

## OBSERVED

A full bootstrap (cranelift backend, LLVM 18 absent) runs the manual pipeline
`seed → bootstrap_main → bootstrap_main`. Stage 3 (the self-host step:
stage2 binary recompiles `bootstrap_main.spl`) fails with exit 1, and the
pipeline falls back to the Rust seed for Stage 4:

```
Stage 3: stage2 → bootstrap_main.spl (self-host)
  warning: stage3 self-host failed (exit 1); using seed for stage 4
Stage 3 unavailable — using seed for stage 4
Stage 4: compiling full CLI (main.spl) with bootstrap compiler...
```

The proximate error in `stage3-native-build.log` is **not** an LLVM symbol
conflict — it is a guard refusing to emit a seed-wrapper:

```
error: bootstrap_main cannot emit a seed-wrapper fallback for build/bootstrap/stage3/<triple>/simple
error: rebuild with the full Simple driver so native-build uses real Simple lowering/codegen
```

The final bootstrap warning attributes the failure to **LIM-010 (LLVM symbol
conflicts)** per `doc/09_report/bootstrap_crash_report_2026_04_01.md`:

```
WARNING: Bootstrap produced a binary but self-host verification (stage 3) failed.
  The stage2 binary cannot yet recompile itself (LIM-010: LLVM symbol conflicts).
  Stage 4 used the Rust seed instead of the self-hosted compiler.
```

## ROOT CAUSE (proximate)

The Stage 2 binary is compiled from `bootstrap_main.spl` — the **minimal** CLI
entry. That binary does not carry the full Simple native lowering/codegen path,
so when asked to `native-build` itself in Stage 3 it can only produce a
*seed-wrapper fallback* (a thin shim that re-invokes the seed) rather than a real
native binary. A guard in the native-build path rejects the seed-wrapper for the
stage3 output and exits 1.

This is distinct from LIM-010 (the historical LLVM-CommandLine-option /
static-constructor conflict at self-hosted-binary startup). The script's warning
text conflates the two: the *current* proximate cause is the seed-wrapper guard
on the minimal `bootstrap_main` entry, regardless of backend.

## REGRESSION NOTE

`doc/09_report/bootstrap_crash_report_2026_04_01.md` records a state where Stage 3
self-host **worked and was SHA256-reproducible**:

```
Stage 3: stage2 → bootstrap_main.spl   ✓ (100 files, 0.8s compile — SELF-HOST WORKS)
  stage2 SHA256 == stage3 SHA256        ✓ (REPRODUCIBLE BUILD)
```

As of 2026-06-17 that no longer holds on `main` (cranelift path). Whether stage3
ever succeeds again depends on `bootstrap_main.spl` gaining the real
lowering/codegen path (or stage2/stage3 being built from the full driver entry).

## REPRODUCTION

```bash
sh scripts/bootstrap/bootstrap-from-scratch.sh
# inspect:
cat build/bootstrap/logs/x86_64-unknown-linux-gnu/stage3-native-build.log
```

Deterministic: two back-to-back runs on 2026-06-17 produced byte-identical stage
progression; the second skipped the cargo rebuild via input-content-hash match,
confirming the failure is independent of any Rust-seed source change.

## IMPACT / WORKAROUND

- The bootstrap still produces working binaries (Stage 4 uses the seed, which is
  a correct compiler). Runtime correctness is unaffected.
- The lost guarantee is **self-host verification** (stage2 == stage3 SHA256) and
  shipping a genuinely self-hosted `build/bootstrap/full/<triple>/simple`.
- No source-side workaround; it is a pipeline/entry-capability gap.

## PROPOSED FIX OPTIONS (hypotheses — verify against actual native-build path)

1. Build stage2/stage3 from the **full driver entry** (`src/app/cli/main.spl`)
   instead of `bootstrap_main.spl`, so the self-host binary carries real
   native lowering/codegen and can emit a true native artifact.
2. Add the missing native lowering/codegen path to `bootstrap_main.spl` so the
   minimal entry can `native-build` without a seed-wrapper fallback.
3. If self-host is intentionally deferred, make the Stage 3 warning state the
   **actual** proximate cause (seed-wrapper guard on the minimal entry) rather
   than attributing it to LIM-010, to avoid misdiagnosis.

## RELATED

- `doc/09_report/bootstrap_crash_report_2026_04_01.md` (LIM-010 + Stage 3 history)
- `doc/06_spec/test/03_system/compiler/stage3_segfault_fix_spec.md`
- `doc/08_tracking/bug/selfhosted_mcp_binary_segfault_2026-06-02.md`

## SHARPENED ROOT CAUSE (2026-06-18)

Deeper investigation re-scoped the stage3 blocker. It is NOT the lean parser
(parser_completion.md G1–G50 is largely DONE — src/lib parses clean) and NOT the
seed-wrapper guard per se. The real blocker is **backend codegen**: the seed's
own native-build (cranelift AOT) of the full compiler produces a binary that is
broken at runtime.

Evidence (build/bootstrap/full/<triple>/simple, the stage4 produced when stage3
falls back to the seed):
- Compiles cleanly: stage4-native-build.log = "791 compiled, 0 failed", linked
  via clang (15 MB). NOT a compile error.
- `--version` / `--help` work (rc=0).
- `-c 'print(1+1)'` and `run <file>` exit **248** (`exit_group(-8)`) with NO
  stdout and NO stderr. `strace` shows NO delegation execve — the binary handles
  `-c` in-process and aborts at exit(-8) before printing anything.
- The SEED interpreting the SAME `main.spl` runs `-c`→`2` fine, so the source
  logic is correct → the cranelift AOT path miscompiles the `-c`/`run` handler,
  or a runtime extern that path needs is not linked in the AOT binary (cf. the
  documented native-AOT gaps: rt_box_int not linked / for-in-array SIGSEGV in
  native AOT).
- The binary IS a delegating stage4 (contains `delegate_to_simple_binary`,
  `_cli_driver_binary`, "set SIMPLE_BOOTSTRAP_DRIVER to a real seed driver"), but
  the 248 happens BEFORE any delegation attempt, so delegation setup is not the
  cause.

seed + llvm-lib is not an escape hatch: `native-build --backend llvm-lib` on the
seed routes through the interpreter dispatch (`native_build_should_use_simple`)
to the `rt_native_build` stub and produces NO binary (verified 2026-06-18).

Consequence: stage2 = seed-AOT of the compiler is non-functional, so stage2
cannot self-build stage3. Real self-host is blocked on **native-AOT codegen/
runtime correctness for the full compiler** (a multi-bug effort), not on parser
completion. The working historical `bin/simple` (461 MB) was built via a
different path (llvm, by a previously-working compiled stage), not reproducible
through the current from-scratch script (which forces seed+cranelift for stage4
whenever stage3 fails).

First concrete step toward repair: minimal-repro the `-c`/`run` AOT miscompile
(which construct or unlinked extern in the eval/run handler returns -8 under
cranelift AOT) and close it; then re-test the seed-AOT full-compiler binary.

## AOT-MISCOMPILE DEBUG PROGRESS (2026-06-18)

Narrowing the seed+cranelift AOT `-c`/`run` → exit(-8)/248 miscompile:
- RULED OUT (all work correctly in minimal native cranelift AOT builds):
  `rt_process_run` subprocess spawn (echo repro: execve count 2, output + code 0),
  for-in over array (sum=60), int-boxing/`str(int)` (42). So the failure is NOT a
  blanket runtime-extern stub.
- LOCALIZED: the `-8` originates in the `-c` → `cli_run_code`
  (src/app/io/cli_commands_part1.spl:64) → `_cli_driver_binary`
  (src/app/io/cli_ops.spl:103) → `_cli_process_run` delegation path. strace of the
  full stage4 binary shows ONLY the binary's own execve then exit_group(-8) — NO
  child spawn, even though `_cli_driver_binary` always runs `_cli_shell`
  (readlink/test/dirname) which would spawn `sh`. So the abort happens before any
  subprocess, inside the full-program compile of this path.
- KEY: the path's primitives all work in isolation; the miscompile only manifests
  in the full module-graph AOT build → a whole-program codegen bug (opt/register/
  layout dependent), not a single bad construct.
- NEXT: instrumented `cli_run_code` + `_cli_driver_binary` with entry/value eprints,
  rebuilding stage4 to pin the exact statement where -8 originates (whether the
  function is even entered, and the driver value). Debug eprints are TEMPORARY
  (revert before any commit).

## AOT-MISCOMPILE DEBUG — SESSION 2 RESULTS (2026-06-18)

Instrumented stage4 (eprints in cli_run_code + _cli_driver_binary, reverted
after) pinned the exit(-8) precisely: `cli_run_code` enters, `_cli_driver_binary`
resolves `driver` to a correct non-empty path, then `_cli_process_run(driver,
["-c", code])` returns `(.0="", .1="", .2=-8)` WITHOUT spawning (strace: execve
count 1 — not even `_cli_shell`'s `sh -c test` self-exec-guard spawns, yet it
returns a non-zero exit_code). So the subprocess-spawn externs (`rt_process_run`
via `_cli_shell`/`_cli_process_run`) yield garbage tuple returns and never spawn —
but ONLY in the full 791-file build.

RULED OUT (each reproduces CORRECTLY in minimal/medium native cranelift AOT —
prints right value, spawns, execve as expected):
- direct `rt_process_run("echo",[...])` and with a slash-path cmd + `["-c",code]`
- for-in over array; int-boxing `str(int)`
- the exact `_cli_shell` pattern: tuple-from-if-else destructure
  `val (a,b) = if cond: (x,[..]) else: (y,[..])` + 3-tuple extern-return
  destructure `val (o,e,c) = rt_process_run(a,b)`
- `--entry-closure` build mode (stage4's mode)
- 2-module CONFLICTING extern signatures (entry decls `->(text,text,i64)`,
  sibling module decls `-> i64`, both called) — still correct.

PRIME SUSPECT (not yet confirmed): `rt_process_run` is declared with CONFLICTING
extern signatures across the real build — 116× `(text,[text])->(text,text,i64)`
but also **3× `-> text`** (driver_api_types.spl:19, driver_api_project_build.spl:19,
app/release/install.spl:18), **2× `-> i64`** (io/vhdl_sffi.spl, lib .../vhdl_sffi),
**1× `(text)->i64`** (wasm_backend.spl:709), **1× `->(text,text,i32)`**
(compiler_rust/lib/std/shell.spl), plus a Simple-level `fn rt_process_run(cmd,
args: i64)->i64` in src/runtime/simple_core/core_process.spl:105. If AOT extern
registration dedupes by symbol name and a divergent signature (esp. the `-> text`
scalar) wins globally, the 3-tuple callsite in cli_ops reads a scalar return as a
tuple → empty strings + -8. The minimal `-> i64` conflict did NOT repro, so if
this is the cause it is the `-> text` variant and/or processing-order dependent.

RECOMMENDED NEXT STEPS (either order):
1. Reconcile all `rt_process_run` extern decls to the canonical
   `(text,[text])->(text,text,i64)` (fix/rename the 3 `->text`, 2 `->i64`,
   1 `(text)->i64`, 1 `->(text,text,i32)` divergent decls — verify each caller),
   rebuild stage4, re-test `-c`/`run`. Low-risk and likely the fix if the
   dedup-hypothesis holds.
2. If still broken: `objdump`/disassemble the `rt_process_run` callsite in the
   full stage4 binary to see the actual emitted call ABI/symbol, and/or dump
   `SIMPLE_DEBUG_EXTERNS` for minimal-vs-full to compare resolved signatures.
Relevant: memory `feedback_rt_extern_registration_and_jit_cross_module_gap`.
