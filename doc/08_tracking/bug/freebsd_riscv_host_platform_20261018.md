# Native RISC-V FreeBSD host target was rejected

Status: fixed in the host resolver; full bootstrap remains in progress.

Before the fix, `bootstrap_stage3_host_platform` in
`scripts/check/lib/bootstrap-stage3/authority.shs` had no RISC-V FreeBSD
case. The live FreeBSD 14.4 guest reports `uname -m = riscv` and
`uname -p = riscv64`; installed native Rust reports
`host: riscv64gc-unknown-freebsd`. Existing cases would return failure.

The resolver now checks processor width for the `riscv` machine family and
returns the Rust host triple for `riscv64`, also accepting an explicit
`riscv64` machine identity. Other widths, unknown processors and a failed
processor query remain rejected.

Validation: the focused shell regression covers both accepted machine
forms, riscv32, unknown and failed processor queries, plus existing amd64
FreeBSD, aarch64 FreeBSD and x86_64 Linux. The corrected resolver was copied
to the live guest and its output matched `rustc -vV`:
`native_platform_rust_host_match=pass`. This proves host identity only.

Provider input/output/cache-read/cache-create token counts: unavailable.
Comparable cohort average and ratio: unavailable; no fabricated accounting.
Reusable guidance: `doc/07_guide/tooling/freebsd_riscv_host_target.md`.
