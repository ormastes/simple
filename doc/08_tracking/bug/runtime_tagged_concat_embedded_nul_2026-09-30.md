# Tagged native concatenation discards embedded NUL bytes

Date: 2026-09-30
Status: focused C runtime regression PASS; original Simple split regression pending.

## Observed failure

A Linux native byte-split regression built by the retained self-hosted compiler
`9088595d5a51191f9895293c8d6c8c17ddefe4d6e12dbf04015b705372b02308`
compiled successfully (3 rebuilt modules, 0 reused), then exited 4 at the
NUL-delimited field assertion. The earlier NUL construction assertion proved
that `char_from_code_inline(0)` produced one byte of value zero. The fixture
constructs its input with `"a" + nul + "한" + nul` before calling `str_split`.
Its success marker was absent. Subsequent assertions were not reached.

The produced binary SHA256 was
`0303382ea6f091f19de662f65960d6a93e4ede5d364f01f160b9421dc2b5844b`.
Disassembly showed calls to `rt_strcat_tagged` at 0x3691, 0x36a0 and 0x36ad,
then the relevant `str_split` call at 0x36ba. The selected `rt_strcat_tagged`
called `strlen` at 0x5547 and 0x5557. These addresses identify this diagnostic
binary; they are not an API contract.

## Cause and correction

`src/runtime/runtime_native.c:rt_strcat_tagged` decoded tagged text into a C
pointer with `rt_interp_cstr`, then used `strlen` to measure it. A valid tagged
text containing embedded NUL therefore lost bytes during concatenation.
For this fixture, source and disassembly indicate the constructed value likely
became `a한` before splitting. No baseline split executable was run, so the
old split path's behavior remains unverified; it shares the same pre-split
concatenation defect.

The fix uses `rt_core_as_string` to validate tagged operands against the string
registry, then reads their stored `data` and `len`. Raw C string and low-value
fallback behavior still uses `rt_interp_cstr`. Inputs remain borrowed and
immutable; output allocation, registration, and trailing zero are unchanged.

## Regression and verification

`test/01_unit/runtime/runtime_concat_nul_test.c` calls the production runtime
for ten cases: embedded NUL in both operands, mixed raw/tagged operands in
both orders, NUL-only strings, empty tagged operands, raw/raw operands, nil in
both positions, and the existing null/low-value behavior. Length and exact
bytes are asserted, including the output's trailing C terminator. Failures
return nonzero; a successful run prints `RUNTIME_CONCAT_NUL_PASS checks=10`.

On a Linux host with a C compiler:

```sh
sh scripts/check/check-runtime-concat-nul.shs
```

The first focused C regression cycle compiled and ran the actual production
runtime twice. Unpatched main source failed eight embedded-NUL cases (exit 1),
including length 2 instead of 6 for two tagged operands and length 0 instead
of 2 for two NUL-only operands. Patched source passed all ten cases (exit 0,
`RUNTIME_CONCAT_NUL_PASS checks=10`). No runtime functions were stubbed.

The original Simple native fixture has NOT been rerun. It retains its NUL
concatenation expression. Three earlier split diagnostic cycles were consumed;
another split native build/run requires the explicitly requested exception.
No Linux bootstrap admission, full SCV timeout resolution, or main/release
runtime parity is claimed.

Measured runtime source SHA256 values (Linux/WSL hosted C, first focused cycle):

- Unpatched main: `960cf8dd55ac3217445571a64124aa907a6f66ad8a56ca7300ad9677cd9bab55`.
- Patched main: `d88bb6a2e1b2a94b38b5b4fed5067728ac91a7bb63edc2bb63bd38c57ccb5998`.

The checker uses GNU/Linux linker flags (`--gc-sections`, `-ldl`, `-pthread`).
This result does not establish Windows or other host runtime verification.
