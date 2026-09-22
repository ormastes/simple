# Stage 4 optional argument and mixed tail revalidation

STATUS: TEST_BLOCKED. The historical defect remains open. No production change
or source-fixed claim is made by this patch.

## Scope and provenance

Worktree: `D:/simple-stage4-optional-tail-20260922`, based on
`e0dd873da1b7828389db4eb60e82972cc8245313` (`origin/main` at lane creation).
PR #1289 owns default-argument changes; this lane changes no shared compiler
owner. PR #1228 was also inspected for overlap.

The retained pure-Simple Stage 2 binary used was
`D:/simple_build/bootstrap-msvc/stage3/x86_64-pc-windows-msvc/stage2-admitted/simple.exe`.
SHA-256: `4a8dd3eb3887b9cb61608dd6cc668dafa18bbd75bd0d98326328df48c6d54db5`.
Its sibling `admission.env` is admitted, identity
`a2eedf0d7d8c2fd955f9726eea77e4535f89bd00645882792a13a45ed12884d4`.
The receipt and retained source/runtime/tool snapshot files were hashed and
matched their recorded digests. The parent provenance and sanity receipts also
name this binary digest. This is the retained admission source snapshot, **not
a compiler rebuilt from this worktree's current source**.

`--help` reports only `compile --format=smf` and `native-build` as supported.
No admitted Stage 4 general CLI was found for interpreter/JIT/SSpec runs. The
Rust seed was not used. The original bug concerns a Rust-seed-produced Stage 4
compiler; Stage 2 results do not validate that producer or close the bug.

## Focused probes

`test/fixtures/stage4_optional_mixed_tail/optional_argument.spl` preserves the
flat optional helper call and guarded `local.id` argument from a match-bound
optional. It checks present, zero, absent, empty operand, and scalar control
values. Callees have no print instrumentation.

`mixed_tail.spl` checks explicit early returns, implicit match arms including
the wildcard, implicit if tails, pure-tail controls, and explicit-tail controls.
`scalar_control.spl` is an independent integer-only negative control. Success
is exit 0; each failed assertion condition has a distinct nonzero exit code.
The separate receiver-transport defect is not covered by these new fixtures.

## Executed evidence

Host: Windows x86_64. Each native build used `SIMPLE_NO_STUB_FALLBACK=1`, a
separate output path and lane-local `SIMPLE_NATIVE_CACHE`. The worktree was
fresh. No shared cache was removed. Command shape:

`<admitted-binary> native-build test/fixtures/stage4_optional_mixed_tail/<case>.spl --backend=<backend> -o build/stage4-optional-tail/<case>.exe`

| Case | Backend | Elapsed ms | Sampled process peak RSS bytes | Exit | Result |
| --- | --- | ---: | ---: | ---: | --- |
| scalar_control | Cranelift | 4610 | 133943296 | 1 | AOT compile error, invalid-heap diagnostic |
| scalar_control | LLVM | 13673 | 134656000 | -1073741819 | Access violation before artifact |
| mixed_tail | LLVM | 13973 | 138047488 | -1073741819 | Access violation before artifact |
| optional_argument (exact guarded field) | Cranelift | 736 | 126513152 | -1073741819 | Access violation after monomorphization |

An earlier optional LLVM probe used explicit `if val` extraction inside the
match arm; its 17343 ms / 126509056 byte / access-violation result is retained in
`llvm.metrics.json` only as a superseded development attempt. It does **not**
represent the final optional fixture or prove the exact field-access behavior.

Logs, metrics, and final fixture hashes are in
`doc/09_report/evidence/stage4_optional_mixed_tail_20260922/`. Process high-water
RSS was sampled every 100 ms through `PeakWorkingSet64`; the final short interval
and child processes are not included. Elapsed time includes process launch.
The machine had concurrent compiler work. These are failure-path observations,
not throughput benchmarks. The scalar control fails independently of the
reported language shapes, so the failures cannot be attributed to this bug.

No executable was emitted or run. The probes reached HIR without diagnostics;
this is not a semantic pass. No before/after production binary exists, so
performance and memory non-regression remain unverified.

## Remaining verification

- An admitted Stage 4 must execute the exact probes through interpreter, JIT,
  native Cranelift and LLVM, with compiler callee debug instrumentation absent.
- The original two-stage reproducer must build the driver with its historical
  producer lane and compile/run the `x5=42` client. A focused Stage 2 failure
  cannot substitute for this observation.
- Linux, macOS, FreeBSD, aarch64, other CPU targets/backends, and GPU paths were
  not executed. The probes are portable source; no platform pass is claimed.
- Keep the existing optional/explicit-return workarounds until the historical
  producer and deployed runtime pass. Receiver-transport needs separate coverage.

Source inspection finds last-expression return handling in the seed MIR
lowerer, but it does not prove optional ABI or staged native behavior. Existing
`bootstrap_mixed_tail_ret_probe.spl` verifies another focused HIR/MIR path;
it likewise cannot establish the original runtime result without execution.

`git diff --check` and the no-executable-specs-under-`doc/06_spec` layout check
are the patch's structural gates. General compiler/MCP verification is not
claimed because no production owner is changed and no general CLI is admitted.

## Independent review

An independent reviewer accepted the patch as TEST_BLOCKED evidence with no
blocking findings. It checked the final fixture hashes, uninstrumented callee
shapes, expected values and failure exits, tracker status, stage distinctions,
and superseded optional LLVM label without rerunning builds. One remaining
coverage gap is a present `id=0` match-bound field call; the direct optional
helper covers zero. Receiver transport remains explicitly untested.
