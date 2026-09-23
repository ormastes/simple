# Bootstrap Stage 4 binary SIGSEGVs at startup — `io.cli_ops.get_args` infinite recursion

## Audit 2026-09-22 — source mitigation present; Stage 4 acceptance remains OPEN

At `origin/main` `e0dd873da1b`, `src/app/io/cli_ops.spl` has no local
`get_args` function. It reexports `std.io_runtime.get_args`, whose canonical
owner in `src/lib/nogc_sync_mut/io_runtime.spl` calls `sys_get_args() ?? []`.
Commit `8a2b5d0d6c7` removed the duplicate wrapper during the I/O migration;
its parent already used direct runtime calls. This establishes the current
source shape, not the identity of the first historical fix or correctness of
every native backend. The older hypothesis below is historical evidence.

The bootstrap script now rejects seed fallback and retains its bounded
Stage 4 `-c 'print(1+1)'` gate. The original recipe describing an accepted
seed fallback no longer describes the current script.

Added regression assets:

- `test/02_integration/runtime/cli_args_facade_termination_spec.spl`: repeated
  calls through the historical facade, consistency with scalar accessors,
  and invalid index controls. Scalar accessors share the provider; this is
  facade consistency coverage, not an independent provider oracle.
- `test/fixtures/runtime/cli_args_facade_native.spl` and
  `cli_args_provider_native.spl`: paired native probes with exact argument
  count and literal expected values, including spaces and an empty argument.
  Both reject a wrong suffix. These are retained, **unexecuted** regressions.

No attested Stage 4 full CLI was available. The deployed Windows executable
identified itself as a Rust seed. Its bounded bootstrap fixture compilation
failed before code generation at inventory admission; the one cold-init
retry also failed. A separately admitted Stage 2 binary had matching
candidate/receipt hashes, but its isolated copy exited at Windows loader
status `0xC0000139` before CLI output. That copy did not reproduce the
admitted runtime loading environment, so it is not evidence of a defect in
the admitted artifact or argv facade. Three bounded build attempts were made;
there were no successful compiler checks to repeat.

See `doc/09_report/stage4_get_args_recursion_audit_2026-09-22.md` for hashes,
timing, sampled process-tree RSS, review, and precise remaining acceptance.
**STATUS: WARN — source mitigation verified by inspection; runtime,
codegen, and performance acceptance unverified. Keep this bug OPEN.**

## Triage 2026-09-13 — STILL OPEN: bootstrap-scoped, cannot be touched or exercised now
- **measured** — Stage 4 artifacts do exist on this host
  (`build/bootstrap/full/x86_64-pc-windows-msvc/{simple.exe,simple_mcp_server.exe,simple_lsp_mcp_server.exe}`),
  but a bootstrap is running concurrently in this workspace, so those files are being
  written and must not be executed or judged mid-run.
- **inferred** — the remaining defects this entry names are in `scripts/bootstrap/**` and
  seed/cranelift codegen, both off-limits to this triage pass. Left OPEN; re-verify after
  the in-flight bootstrap finishes.

- **Id:** bootstrap_stage4_get_args_infinite_recursion_coredump_2026-06-21
- **Status:** Open native acceptance; current source mitigation confirmed 2026-09-22; guarded 2026-06-22
- **Severity:** P1 — a fresh `bootstrap-from-scratch.sh --pure-simple` produces a
  Stage 4 `build/bootstrap/full/<triple>/simple` that **segfaults on every
  invocation** (even `print(1)`), in both interpret and JIT mode. There is no
  working build→run loop from this path, which blocks validating/deploying any
  self-hosted compiler change (e.g. the self-hosted f64 codegen port, see
  `f64_self_hosted_call_result_codegen_2026-06-21.md`).
- **Found:** 2026-06-21
- **Component:** `app.io.cli_ops.get_args` (argv accessor) + seed native codegen
  (`src/compiler_rust`) that compiled it; Stage 4 build path in
  `scripts/bootstrap/bootstrap-from-scratch.sh`.

## OBSERVED

```
$ sh scripts/bootstrap/bootstrap-from-scratch.sh --pure-simple   # Stage 3 self-host fails, Stage 4 built by seed
$ printf 'fn main():\n    print(1)\n' > /tmp/triv.spl
$ build/bootstrap/full/x86_64-unknown-linux-gnu/simple run /tmp/triv.spl
Segmentation fault (core dumped)            # rc=139
$ SIMPLE_EXECUTION_MODE=interpret build/.../simple run /tmp/triv.spl
Segmentation fault (core dumped)            # rc=139  (crashes in BOTH modes)
```

gdb backtrace — unbounded self-recursion (same return address repeating →
stack overflow):

```
Program received signal SIGSEGV, Segmentation fault.
0x00000000004d686c in io.cli_ops.get_args ()
#0  0x...4d686c in io.cli_ops.get_args ()
#1  0x...4d6871 in io.cli_ops.get_args ()
#2  0x...4d6871 in io.cli_ops.get_args ()
...                                         # identical frame repeats to stack exhaustion
```

The crash is at argv parsing during CLI startup, **before** any program runs —
which is why both execution modes die identically.

## ANALYSIS

- `io.cli_ops.get_args` is compiled into infinite self-recursion by the seed
  native-build that produces Stage 4. The likely shape is a wrapper/forwarding
  function the seed lowers as a call to itself (missing tail/leaf resolution, or
  a same-name self-dispatch) instead of the runtime argv primitive. Definition
  lives under `src/app/io/cli_ops` (re-exported via `src/app/io/mod.spl`); the
  pure-Simple argv source is `src/lib/nogc_sync_mut/io_runtime.spl:172`.
- **The deployed `bin/simple` does NOT crash** (`run /tmp/triv.spl` → `1`,
  rc=0), so a runnable Stage 4 is producible by some path; this specific
  `--pure-simple` seed-build path miscompiles `get_args`. The seed used was
  `src/compiler_rust/target/bootstrap/simple`.

## CONTRADICTS EXISTING DOC

`bootstrap_stage3_selfhost_seed_wrapper_fallback_2026-06-17.md` states the
Stage-4 fallback "still produces working binaries (Stage 4 uses the seed, which
is valid)" and is "Not a runtime-correctness bug." This repro shows that
assumption no longer holds for `--pure-simple`: the seed-built Stage 4 binary is
not runnable. That doc's severity downgrade should be revisited.

## IMPACT

- Blocks self-host verification AND any "build self-hosted from source → test"
  loop. Directly blocks the self-hosted f64 codegen port.

## REPRO / FIX CHECKLIST

1. Reproduce: `sh scripts/bootstrap/bootstrap-from-scratch.sh --pure-simple`
   then run the fresh `build/bootstrap/full/<triple>/simple` on any program.
2. Disassemble `get_args` (gdb `disas`) to confirm the self-call, and diff its
   MIR/codegen vs the deployed (working) `bin/simple`.
3. Determine why this seed build lowers `get_args` to self-recursion (seed
   version? a forwarding alias resolving to itself?); fix in the seed codegen or
   the `cli_ops.get_args` definition.
4. Add a Stage-4 smoke gate to `bootstrap-from-scratch.sh`: run
   `<stage4> -c "print(1+1)"` and fail the build if it does not print `2`.
   - Done 2026-06-22: `scripts/bootstrap/bootstrap-from-scratch.sh` now smokes
     `${full_bin}` immediately after Stage 4 and exits before deploy/MCP work if
     the new binary cannot execute code. Guarded by
     `test/01_unit/compiler/bootstrap/stage4_smoke_gate_spec.spl`.

## REFERENCES

- `doc/08_tracking/bug/bootstrap_stage3_selfhost_seed_wrapper_fallback_2026-06-17.md`
- `doc/08_tracking/bug/f64_self_hosted_call_result_codegen_2026-06-21.md` (blocked by this)
- `doc/09_report/bootstrap_crash_report_2026_04_01.md` (LIM-010 history)
