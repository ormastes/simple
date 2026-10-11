# Target 6 array-aware CAS writer cohort (2026-10-11)

## Change and correctness

The SOSIX byte-stage API keeps its Simple signature. Its hosted implementation now borrows packed `[u8]` storage directly, or narrows boxed byte values into at most 1 MiB scratch, then creates the private stage exclusively and checks every positioned write. This replaces one Simple-to-C byte setter call per byte. The admitted no-stub Stage2 LLVM fixture passed from a fresh root with literal, pushed, and repeated arrays; it verified NUL/high bytes and a 1,048,583-byte object spanning the chunk boundary. This is a runtime boundary optimization; the CAS and archive admission rules remain in Simple.

## Paired evidence

Host: Linux aarch64. The same 1,048,583-byte CAS/archive executable fixture ran 30 paired samples per binary, alternating order and deleting its owned fixture root before each sample. Time is Node monotonic wall time around the process; peak RSS is `/usr/bin/time %M`. Both binaries were built with the admitted Stage2 LLVM no-stub entry closure. The raw-buffer baseline SHA-256 is `d1a3fba5502ab763ba0bb450651a7d5a3bdd99e5265ca66a34b42fb6e8fcd889`; the array-aware candidate SHA-256 is `6ec383a64fc99914470d8b5383a4be1e056c1203cf3d577b1a5e6407532ea8e7`.

| Metric | Raw-buffer baseline | Array-aware candidate |
|---|---:|---:|
| Executable bytes | 113,848 | 111,560 |
| Wall p50 | 569.745 ms | 556.895 ms |
| Wall p95 | 579.113 ms | 572.402 ms |
| Peak RSS across samples | 13,968 KiB | 14,004 KiB |

`time_ratio = 0.988411`, `memory_ratio = 1.002577`, normalized sum `= 1.990988`. A deterministic 10,000-resample paired bootstrap gives a 95% interval of `[-0.021890, -0.006756]` for `(sum - 2)`. The focused tradeoff improves the combined rule beyond this cohort’s sampling noise, though peak RSS rises by 36 KiB. Packed objects avoid the former raw scratch allocation; boxed input remains bounded at 1 MiB. Steady RSS is not meaningful for this short process and was not measured.

Raw samples and the cohort driver are `/tmp/simple-target6-cas-writer-cohort.json` and `/tmp/simple-target6-cas-writer-cohort.js`; the candidate build log is `/tmp/simple-target6-cas-array-native-build-20261012.log`. The later pushed-array correctness build log is `/tmp/simple-target6-cas-pushed-build-20261012.log`. These local artifacts are diagnostic evidence, not immutable release artifacts.

## Limit

This cohort measures a focused CAS/archive fixture. It does not prove full CLI V3 publication, warm native compilation, startup, interpreter SPipe execution, or Item 6 release performance budgets. The admitted Stage2 tool has no `run` or `test` command, so the authored SPipe spec remains unexecuted.
