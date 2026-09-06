# CPU SIMD operation matrix — 2026-08-12

Status: **FAIL for 8K/80 admission; operation evidence only**.

- Revision: `27dfef19cca` plus current worktree
- Host: x86_64, detected feature AVX2
- Runner: `bin/simple test ... --mode=interpreter`
- Workload: one 7680-pixel row, 31 samples per operation
- Correctness: scalar/SIMD checksums matched for every operation
- Provider: native-row gate true; operation hit counters nonzero
- Full-frame readback: not performed
- RSS: not recorded
- Fallback: no backend fallback receipt is exposed by this row harness

| Operation | Scalar p50/p95 ns | SIMD p50/p95 ns | Hits | Linear 4320-row p95 projection |
|---|---:|---:|---:|---:|
| fill | 20,829,042 / 21,190,152 | 16,268,027 / 16,536,740 | 62 | 71,438,716,800 ns |
| copy | 21,054,203 / 21,802,753 | 8,098,185 / 8,316,603 | 31 | 35,927,724,960 ns |
| source-over constant | 941,035,576 / 989,334,272 | 8,383,220 / 12,085,283 | 31 | 52,208,422,560 ns |
| source-over image | 1,032,419,887 / 1,074,094,843 | 8,032,891 / 8,732,056 | 31 | 37,722,481,920 ns |

The projections are diagnostic multiplication, not measured full-frame timing.
They exceed the 12.5 ms budget by thousands of times and cannot establish an
8K/80 pass. This execution path also routes externs through the interpreter
bridge, so native compiled ISA, AArch64/NEON, RISC-V/RVV, bare/QEMU, p95 RSS,
and framebuffer checksum evidence remain required.

Focused spec verdict: 1/1 PASS. O3 analysis completed with 25 opportunities.
