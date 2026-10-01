# Stage 4 get_args recursion audit — 2026-09-22

Scope: `bootstrap_stage4_get_args_infinite_recursion_coredump_2026-06-21`.
Base: `e0dd873da1b7828389db4eb60e82972cc8245313`, isolated D: worktree.
No production source changed. The historical local wrapper is absent;
`8a2b5d0d6c7` replaced it with the canonical reexport. Its parent already
called runtime primitives directly. This audit does not establish that the
original seed lowering bug is fixed on every target.

## Executed evidence

The shared deployed Windows executable was copied before probing. SHA256:
`6094dcae291aa984973ccd681f956e67a7a60543ab99f76a29313fbbfdee96d1`.
It reports `Simple Language v1.0.0-rc.1` and explicitly warns that it is a
Rust bootstrap seed. It was used only for bootstrap compilation diagnostics.

| Probe | Exit / result | Elapsed | Sampled peak tree RSS |
|---|---|---:|---:|
| Seed provider native-build | 1, compile-event-journal-missing | 7.561 s | 298,516,480 bytes |
| Same build, inventory cold init enabled | 1, cold-init-listed-no-sources | 6.506 s | 304,971,776 bytes |
| Isolated admitted Stage 2, --version baseline | 0xC0000139, before output | 0.752 s | 3,182,592 bytes |
| Same Stage 2, provider native-build | 0xC0000139, before output | 0.524 s | 3,182,592 bytes |

Each build used a 30-second external process-tree deadline and
`SIMPLE_NO_STUB_FALLBACK=1`. The cold-init retry additionally set
`SIMPLE_SCV_INVENTORY_COLD_INIT=1`. Build arguments were:

`native-build --source test/fixtures/runtime/cli_args_provider_native.spl --entry test/fixtures/runtime/cli_args_provider_native.spl --output D:/simple-argv-audit-evidence/provider.exe`

Measurement used redirected streams, a monotonic wall clock, 20-ms sampling
of working sets, and descendant discovery at roughly 500-ms intervals.
Seed probes observed two processes; Stage 2 probes observed one. Discovery
overhead is included. RSS is a sampled lower bound, not a kernel-recorded
whole-tree maximum; very short-lived children may be missed. Local raw logs
and the measurement helper remain at `D:/simple-argv-audit-evidence/`.
No candidate program was produced, so **no runtime speed/memory regression
comparison is available**. The failed-loader baseline cannot serve as one.

The Stage 2 source artifact was
`D:/wk-stage2-llvm-c-link/.simple/storage/build/bootstrap/stage2/x86_64-pc-windows-msvc/simple.exe`.
Its SHA256 matched the provenance and sanity receipts:
`be0ad06d6a68b466785eae2c1cb966f61c7026dd5fae8242591353760d72c7c2`.
The admission receipt hash also matched:
`e486b6e40a401ee49f72ecc2498f37adffd634abfc61f7405c72f65ad8e47406`.
Source/runtime/tool snapshot files and sanity/receiver evidence files matched
the admission hashes. This binds those files to the receipt; it does not
assert the current worktree equals that snapshot. The isolated copy lacked
the admitted runtime loading environment; its loader failure is not an argv
result. The three-build-attempt cap was reached without codegen acceptance.

## Review and remaining acceptance

Independent reviewer `argv_review` accepted the files as draft, unexecuted
coverage and required exact native argc if claiming full preservation.
Both fixtures now require exactly five arguments (argv0 plus four literals).
The reviewer confirmed scalar accessors share the provider and cannot be
treated as an independent oracle. Native fixtures supply literal oracles.

TODO-ARGV-STAGE4-ACCEPTANCE (OPEN, owner: bootstrap verification):

1. Produce an attested full Stage 4 CLI from the current source and retain
   candidate/source/runtime/tool receipt identities. Run startup arithmetic
   and the integration spec with external deadline and memory limits.
2. Compile both native fixtures with stub fallback disabled. Run positive,
   wrong-value, and missing-argument cases; inspect emitted IR/disassembly
   to exclude a facade self-call and identify its runtime target.
3. Repeat on Windows x86_64 and the original Linux x86_64 host. Add macOS
   AArch64 and supported cross-target backend controls. Unavailable hosts or
   CPU targets must remain explicitly unverified, including ELF/COFF/Mach-O
   symbol binding, rather than inheriting a source inspection PASS.
4. Measure paired facade/provider elapsed time and peak process-tree memory
   under the same build/runtime configuration. Retain a pre-change artifact
   baseline and a meaningful regression budget; do not compare failed builds
   with successful argv execution.

STATUS: WARN. Source mitigation present; Stage 4 execution, backend controls,
manual generation, and performance acceptance remain unverified. Bug stays OPEN.
