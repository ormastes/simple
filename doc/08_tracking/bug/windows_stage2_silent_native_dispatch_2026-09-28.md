# Windows Stage2 positional native build exits silently after format dispatch

Status: OPEN; focused forensic evidence, no bootstrap admission or release PASS.
Date: 2026-09-28. Source revision: `a4aa33c3492ce19e3b6a56766405fa7bc3a1a41b`.

## Preserved failure

The final of three full Windows build cycles compiled/linked Stage2 but rejected
the candidate during `hello-world-positional-build`, bootstrap mode 0, LLVM.
The first three frontend probes passed. The hello-world collector records
`reason=child-exit`, `raw_status=1`, `native_exit_status=1`, 7400 captured bytes,
and a 180-second limit. This was not timeout or output truncation.

Evidence root:
`D:/dev/simple-windows-bootstrap-20260927/build/bootstrap/windows-linux-20260927/windows/`.

- Candidate: `stage2/x86_64-pc-windows-msvc/simple.exe.rejected`.
- Candidate SHA-256: `352566f7104657fa5497414ca926201a649a639f3314b3561b952a0e8fa55128`.
- Receipt: `stage3/x86_64-pc-windows-msvc/stage2-sanity.env`.
- Per-probe status: same directory, `stage2-sanity.env.frontend-bootstrap-0.status.env`.
- Log: same directory, `stage2-sanity.env.frontend-bootstrap-0.log.hello-world-positional`.
- Collector receipt: the log path plus `.bounded.env`.

The last original marker says `weave_aop ... current=done`; AOP completed.
Its position alone does not establish an AOP defect.

## One focused replay

Detached isolated worktree:
`C:/Users/ormas/dev/win-admission-forensic-20260928`.
The D evidence checkout was read only. The candidate was copied byte for byte
into `build/native_probe/admission-forensic/candidate.exe`; its hash matches.
No full bootstrap, seed invocation, source change, or second compiler probe ran.

Reproduction script and outputs are retained under that isolated worktree:

- `build/native_probe/admission-forensic/replay.ps1`.
- `build/native_probe/admission-forensic/trace.stdout.log`.
- `build/native_probe/admission-forensic/trace.stderr.log`.
- `build/native_probe/admission-forensic/trace.exit.txt`: `1`.
- stderr SHA-256: `c1077bfda6230e5d75f135dd4a2727d3eb4582d93b5713e90e59bb11eff1b49d`.

The script preserves the admission argv shape and bootstrap mode, with separate
cache/output/temp paths and `SIMPLE_COMPILER_PHASE_PROFILE=1` plus
`SIMPLE_COMPILER_TRACE=1`. The fixture contains only `fn main(): print("hello")`.
The effective argv was `native-build --backend llvm --runtime-bundle
core-c-bootstrap --entry-closure --cache-dir <isolated-cache> --mode one-binary
scripts/check/cert/redeploy_gate/fixtures/hello_world.spl --output
<isolated-hello.exe>`. The replay set `SIMPLE_BOOTSTRAP=0`,
`SIMPLE_FRONTEND_DELEGATED=1`, `SIMPLE_NO_STUB_FALLBACK=1`,
`SIMPLE_LIB=<checkout>/src`, both compiler trace variables to `1`, and LLVM
23.1.1's DLL directory first on `PATH`.
This is a diagnostic reproduction, not a new admission receipt: the original
scrubbed home/environment and bounded collector are not replicated completely.

An initial launch never entered the compiler: loader status `0xc0000139`
(`-1073741511`) occurred with the shell's LLVM 18 selection. Explicit LLVM 23.1.1
PATH selection, consistent with the original transcript, permitted the actual
replay. The candidate imports `LLVM-C.dll`. The initial empty logs are retained
as `stdout.log`, `stderr.log`, `exit.txt`; they are not compiler failure evidence.

The replay's final checkpoints were:

```text
[BOOTSTRAP-PHASE] +4770ms aot:lower_to_mir:module:done idx=0 module=scripts.check.cert.redeploy_gate.fixtures.hello_world functions=-1
[BOOTSTRAP-PHASE] +4774ms aot:weave_aop:done
[BOOTSTRAP-PHASE] +4775ms aot:debug_trace:done
[BOOTSTRAP-PHASE] +4775ms aot:output:done
[BOOTSTRAP-PHASE] +4776ms aot:backend_name:done
[BOOTSTRAP-PHASE] +4776ms aot:format:done
```

There is no `[NATIVE]` marker or printed error. The earlier HIR error counters
are zero. The observed `functions=-1` is a separate suspicious value from
`lowered_entry.functions.len()`; it does not establish which operation is wrong.

## Narrowed boundary and next discriminating diagnostic

`src/compiler/80.driver/driver_aot_pipeline.spl:196` logs format completion.
Subsequent untraced code checks bootstrap-entry identity and output-format
predicates, then dispatches to native/SMF/self-contained output.
`driver_aot_native_output.spl:1542` extracts the context and may open
`BackendSessionOwnedLeaseV2` before reaching its first `[NATIVE]` message.
`driver_backend_plugin_selection.spl:45` routes `llvm` through this versioned
backend admission. A rejection there should return `CodegenError`.

`src/app/cli/bootstrap_main.spl:492` interprets the returned `CompileResult`.
Its failure branch prints each `compile_result_errors(result)` element and
returns 1; an empty errors array therefore gives exactly the observed silent
exit. `src/compiler/00.common/driver_compile_result.spl:38` returns an empty
array for an unmatched variant. Corrupt enum/aggregate transport is a candidate
explanation, not a demonstrated root cause. Backend refusal, wrong format
dispatch, and a malformed MIR carrier remain distinguishable alternatives.

The next authorized diagnostic should instrument only these boundaries:

1. Log each output-format predicate and selected dispatch, then entry to
   `compile_to_native`, `_extract_driver_ctx` completion, and session `open`
   success/error. This separates format transport from native/session failure.
2. Log MIR function counts before returning from `lower_module_transient_scoped`,
   before and after its `Result.unwrap`, and at native entry. A change across a
   boundary identifies the first corrupt carrier instead of blaming AOP.
3. At the bootstrap caller, print the success predicate and error-array length
   before the loop, and emit an explicit fallback diagnostic when failure has
   zero messages. That establishes whether the silent exit is a lost result.

Use an isolated focused instrumented binary or symbols from a retained matching
link. The rejected PE has no COFF symbol table and no exports, so symbolic
breakpoints against it cannot be assumed to resolve. Do not restart the full
three-cycle bootstrap workflow or certify this rejected candidate.

The eleven RtHal unresolved stubs are preserved in the adjacent
`simple.exe.stubbed_symbols.txt`; this replay did not establish that any were
called. Removing or bypassing them would not be an evidence-based fix.

## PR relationship

PR #1991 remains OPEN/DRAFT. Its reviewed source patch was replayed unchanged
onto main `97020f7badf5a4fac26943bfad83bf6ae32222b1` as
`9ca460626a620b4777542c2c213fe0d4e4ac4301`; the PR passed its Code Idiom
gate. That integration did not rerun full bootstrap.
This report supplies no admission-based reason to promote or land the PR.
Its collection-removal and receiver changes must be judged on their independent
focused coverage; they do not resolve the failure documented here.
