# Stage2 borrow-check verdict reads a stale receiver

Date: 2026-09-22. Baseline: `5f6d411322ec978f776292d450d169cd5c5a416e`.
Status: focused containment and native projection PASS; independent Astra
review PASS. Full rebuilt Stage2 admission remains pending. General native
zero-argument receiver transport is OPEN.

## Exact failure and causal evidence

The parent Stage2 native build completed (3 compiled, 896 cached). Admission
then failed `hello-world-positional-build` with raw exit 1, without a signal or
a printed borrow diagnostic. The retained rejected candidate is:

`/Users/ormastes/simple-tmp/macos-bootstrap-restart-20260922/build/evidence/macos-enforced-bd544/stage2-autovectorize-5f6d411/simple.rejected`

SHA-256: `6edd6dff04ab9294f01ccaad241d926b902ea75c0e55706745a6404faa798c5f`.

Admission argv is `native-build --backend cranelift --runtime-bundle
core-c-bootstrap --entry-closure --cache-dir <isolated-probe-cache> --mode
one-binary scripts/check/cert/redeploy_gate/fixtures/hello_world.spl --output
<isolated-probe-output>`. Environment sets `SIMPLE_BINARY`, `SIMPLE_BIN`,
`SIMPLE_BOOTSTRAP_DRIVER`, and `SIMPLE_FRONTEND_DELEGATE` to that candidate,
`SIMPLE_FRONTEND_DELEGATED=1`, `SIMPLE_NO_STUB_FALLBACK=1`,
`SIMPLE_EXECUTION_MODE=` (empty), `SIMPLE_NATIVE_BUILD_FORCE_WORKER=0`,
`SIMPLE_BOOTSTRAP=0`, and `SIMPLE_LIB=<worktree>/src`.

The isolated diagnostic replay additionally enabled
`SIMPLE_COMPILER_PHASE_PROFILE=1` and `SIMPLE_COMPILER_TRACE=1`, with the pinned
LLVM 23 environment. It reached `aot:lower_to_mir:done`, then
`aot:borrow_check:start`, and exited normally with failure. Elapsed time was
1.40 seconds, maximum RSS 60,555,264 bytes. No new compiler crash was involved.

LLDB proves `CompilerDriver.borrow_check` returns false. In the rejected
machine code, offsets +200/+204 load `self.ctx` into x15; +208/+212 overwrite
x15 with `CompileContext.has_errors`; +216 calls it without setting x0. The
callee reads its supposed context's error count at offset 0xf8. In one captured
execution the actual context was `0x102ddc150`, with count **0**, while the
callee received `0x76ef03da1`; its decoded count slot held `0x76ef0b6a0`.
Consequently `has_errors()` returns true and the borrow phase returns false.
The actual error array is empty, explaining the silent CLI failure.

Three `malformed_hir_type at walk_type` messages precede this failure. They
are **not the cause of this borrow verdict**: MIR lowering returned success
and the authoritative context count remained zero. Their own root cause and
semantic impact remain unresolved; this change does not remove them or prove
that later code generation is correct. The failing admission did not retain
a textual MIR dump. Exact native call disassembly and live receiver values
establish the boundary observed here; the first compiler layer losing the
argument remains to be identified from the producing MIR/CLIF.

## Narrow correction and limits

The success epilogue now reads `self.ctx.error_count_value == 0` directly.
The count is initialized to zero and incremented by `add_error`; this preserves
the verdict under its nonnegative invariant. Existing skip behavior and
diagnostic collection remain intact. This adds no allocation, scan, loop,
cache, or fallback and removes one unsafe receiver call.

This is an explicit containment, not a repair of general native method-call
lowering. Prior evidence is recorded in
`native_zero_arg_method_receiver_not_marshalled_2026-07-19.md`,
`fv2_gate_collector_selfhost_compile_segv_2026_08_12.md`, and
`simpleos_stage3_native_ast_mode_cache_segfault_2026-08-20.md`.
Current MIR receiver helpers already append the receiver, so changing those
helpers without the producing MIR would risk duplicating an existing argument.

## Minimal native red/green evidence

Worktree: `/Users/ormastes/simple-tmp/macos-stage2-mir-exit1-20260922`.
Evidence directory: `build/evidence/stage2-mir-exit1/`.
Reproduction and extraction recipe:
`test/fixtures/native/borrow_check_status/README.md`.

The exact production method was automatically extracted into a two-module
projection with fixture context/checker dependencies. The synthetic context
does not reproduce the real aggregate layout; it tests the same call shape
and source method. Support/scenario files are identical across red and green.
Both variants were built by the same frozen bootstrap authority:

`/Users/ormastes/simple-tmp/macos-bootstrap-restart-20260922/build/bootstrap/macos-enforced-bd544-stage2/stage3/aarch64-apple-darwin/stage2-runtime-authority/simple`

Producer SHA-256:
`3ff20095e350af7f0b5cc150fd59872b073955eced1e10f3e264ca4a1e37c0a6`.

Native red exits **11** on the clean case. Its disassembly repeats the exact
missing-x0 receiver sequence. Green exits **0**, prints
`borrow-check-status-pass`, and covers clean completion, an existing error,
a newly collected error with retained text, and the existing skip path. Green
disassembly loads the actual nested context, reads its count, and compares
against zero without invoking `has_errors`.

| Measurement | Red | Green |
|---|---:|---:|
| Compiled / cached / failed modules | 2 / 0 / 0 | 2 / 0 / 0 |
| Build elapsed including watchdog setup | 3.25 s | 3.13 s |
| Build sampled process-tree peak RSS | 200,480 KiB | 204,912 KiB |
| Native run exit | 11 | 0 |
| Run sampled process-tree peak RSS | 2,528 KiB | 2,576 KiB |

Every successful build/run collection records `observer_errors=0` and
`quiescent=1`. Builds used a 180-second deadline, runs 20 seconds, and the
5,859,375 KiB cap. Both builds are below the ordinary decimal 1 GB target.
Green executable-only `/usr/bin/time -l` reports 0.39 seconds and 8,732,672
bytes maximum RSS. Red's time measurement encloses the watchdog and is not
directly comparable; short-run sampling can miss peaks. These single runs
support bounded resource use, not a speedup or general performance claim.

Two initial fixture-setup failures are preserved: reserved parameter `skip`,
then a support import placed outside the entry's relative module root. Both
were corrected before the baseline native run and before production edits.
There was one production fix cycle, no bootstrap/main rebuild or cache sharing.

Artifact SHA-256:

- Red native: `5618efa1fac66e04e07e497615337566d6ab1bd38c564897cf6d3c201fe41f62`.
- Green native: `d38668a44f25e678d72010ef6ec30eb5fa545ca9399ee541d27bfa825f28c47f`.
- Fixed owner: `30776ddc025c8df23e9f5df24f8e383738b39c9203c38f44a1d9625ea8996f93`.

This bootstrap-only projection does not admit the candidate. Full compiler,
library, MCP/LSP checks and actual Stage2 admission remain blocked until the
parent rebuilds and admits a compiler. No seed-based general SSpec pass,
production verification, Stage3 eligibility, deployment or push is claimed.

Independent Astra review verified exact extraction, unchanged dependency and
scenario fixtures across red/green, matching hashes, both disassemblies,
behavioral assertions and resource caveats. No blocking findings. Working and
staged direct-env audit, whitespace, and executable-spec layout checks passed;
`doc/06_spec` contains zero executable `_spec.spl` files. These are scoped
commit checks, not a production verification PASS.
