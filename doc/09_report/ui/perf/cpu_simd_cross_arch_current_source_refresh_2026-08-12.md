# CPU SIMD cross-architecture current-source refresh — 2026-08-12

Status: **PARTIAL**. Compiled kernel correctness passes; Simple frames,
physical-device performance, bare-system display, and 8K/80 remain unproved.

- Worktree base revision: `27dfef19cca`
- Runtime source SHA-256: `0eab99e0764f61d9fc8638dec0df3e6a68aabc5aca879b5e35aba8070cb67efb`
- Source dispatch contract: PASS
- Runtime compilation: x86-64 PASS; AArch64 PASS; RV64 PASS; RV64GCV PASS

| Target | Execution | Helper oracle | In-place span ABI | Row scheduling | Binary SHA-256 |
|---|---|---|---|---|---|
| x86-64 | host | PASS | PASS | PASS | `097ef1fe07d285e6f0de5d8bb6d568c6b6ae89a7211634d136e0f30b23c70977` |
| AArch64/NEON | QEMU user | PASS | PASS | PASS | `1a7c8339e33c23955c6fe8ac25300a7dc3ab20e467769bdc9baee0c45558de35` |
| RV64GCV | QEMU user, VLEN 128 | PASS | PASS | PASS | `416488ebd2d65904bf2148df322eb11f344708be8f90ff4046ee41ef8dd21fe2` |

Command class: `check-cpu-simd-engine2d-arch-matrix.shs` with target builds
enabled and Simple-frame execution skipped. Artifacts are under
`build/cpu-simd-engine2d-arch-matrix-codex-current/`.

The matrix reports `partial`, with three Simple architecture rows unavailable
and zero target-binary failures. QEMU establishes instruction-path correctness,
not Arm/RISC-V hardware throughput. There is no framebuffer presentation,
readback checksum, RSS, or full 7680x4320 timing receipt in this refresh.
