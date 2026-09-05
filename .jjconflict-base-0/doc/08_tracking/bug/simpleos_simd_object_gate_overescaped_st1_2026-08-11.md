# SimpleOS SIMD object gate rejects valid AArch64 `st1`

## Status

Resolved for the ARM64/x86 static prerequisite gate on 2026-08-11. Live guest
and RV64 coverage remain open.

## Reproduction

```sh
sh scripts/check/check-simpleos-qemu-engine2d-simd-kernels.shs
```

The script exits 1 without a diagnostic at its AArch64 `st1` grep. `sh -x`
identifies this predicate:

```sh
grep -Eq '[[:space:]]st1[[:space:]]+\\{' arm64.dis
```

The single-quoted ERE contains two backslashes. It does not match the valid
instruction emitted by clang:

```text
c4: 4e040c40  dup v0.4s, w2
c8: 4c007800  st1 {v0.4s}, [x0]
```

The intended literal-brace ERE is `[[:space:]]st1[[:space:]]+\{` (one
backslash as received by grep), or an equivalent fixed-string check.

## Independent prerequisite audit

Using the same compile flags, all remaining object predicates pass:

- AArch64: `dup v0.4s` and `st1 {v0.4s}` are present.
- x86-64: `pshufd` and `movdqu` are present.
- Both objects export `rt_gui_simd_fill_enabled`, `rt_gui_simd_fill_hits`,
  `rt_gui_simd_fill_chunks`, and `rt_gui_simd_fill_tail_pixels`.

This proves only static kernel admission. It does not provide the guest hit/
chunk receipt, QMP capture, bare timing, or 8K/80 evidence required by the
script header and rendering completion gate.

## Ownership note

The checker now uses the one-backslash ERE and passes its real object probe.
RV64 now has a runtime-VL `rt_gui_fill4` using `vsetvli`, `vmv.v.x`, and
`vse32.v`; x86 gained the scalar-parity receipt already present on ARM64 and
RV64. The checker requires instruction bodies plus enabled/hit/chunk/tail/parity
symbols on every architecture and emits three machine-readable pass rows.

The remaining work is live QEMU guest hit/chunk/parity and display capture
receipts; static objects alone remain insufficient for 8K/80 admission.
