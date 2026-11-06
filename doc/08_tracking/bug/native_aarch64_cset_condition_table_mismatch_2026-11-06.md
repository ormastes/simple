# Native AArch64: ordered compares encode the wrong CSET condition

- Found: 2026-11-06, XRay PR5b in-process e2e (`work/xray-aarch64-runtime-20261106`).
- Status: open (not XRay; reproduces with `--xray` off).

## Cause

`src/compiler/70.backend/backend/native/isel_aarch64.spl:31-36` numbers the
CSET conditions EQ 0, NE 1, LT 2, LE 3, GT 4, GE 5, but
`encode_aarch64.spl:44-58` (`invert_cond`) expects the A64 condition field
(EQ 0, NE 1, GE 10, LT 11, GT 12, LE 13). LT=2 falls to `cond ^ 1` = 3, so
`x < 0` is emitted as `cset hs` (unsigned >=), and LE/GT/GE are wrong the
same way. Only `==` / `!=` are correct.

## Repro

`fn scaled(x: i64) -> i64: if x < 0: return 0 - x / x * 3` built with
`--native --backend=native` (shared) returns `scaled(9) = -9` (expected 27);
disassembly: `cmp x19, x21; cset x20, hs; cbnz x20, <neg path>`.

## Fix direction

Make isel use the encoder's A64 condition values (one shared table). This
changes every native aarch64 object containing an ordered compare, so the
XRay off-identity baseline must be regenerated in the same change.
