# Engine2D RVV boxed opaque blend candidates regress under QEMU

Date: 2026-08-11

Two direct boxed/tagged opaque-span implementations were tested using
`riscv64-linux-gnu-gcc -O3 -march=rv64gcv` and QEMU RVV 1.0 with VLEN 256.
Both passed exact pixel parity and emitted native SIMD receipts.

| Classification | Vector p50 | Scalar p50 | Ratio |
|---|---:|---:|---:|
| scalar alpha scan per VL | 357,213 ns | 345,951 ns | 0.968x |
| RVV mask + population count | 454,930 ns | 397,790 ns | 0.874x |

Workload: 7,680 opaque pixels over 500 frames. Both candidates were reverted;
shipping either would violate the semantics-preserving optimization gate.

RVV fill and copy remain vectorized. Blend needs a different representation or
an end-to-end batch design that amortizes QEMU/native vector setup and avoids
per-block mask reductions. Physical RISC-V hardware evidence is still missing.

Opaque constant blend is excluded from this blocker: it now delegates directly
to RVV fill and measures 2.053x its scalar src-over oracle under the same QEMU
configuration. The open defect concerns image spans and mixed alpha.
