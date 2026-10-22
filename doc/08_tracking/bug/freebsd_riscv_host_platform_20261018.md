# Native RISC-V FreeBSD host target was rejected

Status: fixed in the host resolver; full bootstrap remains in progress.

Before the fix, `bootstrap_stage3_host_platform` in
`scripts/check/lib/bootstrap-stage3/authority.shs` had no RISC-V FreeBSD
case. The live FreeBSD 14.4 guest reports `uname -m = riscv` and
`uname -p = riscv64`; installed native Rust reports
`host: riscv64gc-unknown-freebsd`. Existing cases would return failure.

The resolver now checks processor width for the `riscv` machine family and
returns the Simple artifact triple for `riscv64`, also accepting an explicit
`riscv64` machine identity. Other widths, unknown processors and a failed
processor query remain rejected.

Validation: the focused shell regression covers both accepted machine
forms, riscv32, unknown and failed processor queries, plus existing amd64
FreeBSD, aarch64 FreeBSD and x86_64 Linux. Follow-up integration found the
first fix in PR #3638 returned Cargo's spelling for Simple artifact paths,
and the main platform detector still lacked FreeBSD's `riscv` family case.
Both owners now normalize to `riscv64-unknown-freebsd`, while the platform
detector separately maps Cargo to `riscv64gc-unknown-freebsd`.

The target-alignment regression compares both owners and Cargo spellings.
The live guest reported `native_simple_target=riscv64-unknown-freebsd`,
`native_cargo_target=riscv64gc-unknown-freebsd`, and
`native_target_alignment=pass`. The same live test confirmed LLVM 23.1.2
is admitted and 23.1.3 is rejected. This proves target alignment, not a
complete bootstrap.

Provider input/output/cache-read/cache-create token counts: unavailable.
Comparable cohort average and ratio: unavailable; no fabricated accounting.
Reusable guidance: `doc/07_guide/tooling/freebsd_riscv_host_target.md`.
