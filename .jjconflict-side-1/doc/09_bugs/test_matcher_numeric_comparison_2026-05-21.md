# Test Matcher Numeric Comparison Bug - 2026-05-21

## Summary

`to_be_greater_than` failed in interpreter-run SPipe specs even when the displayed
actual value was plainly greater than the expected value.

Observed failures:

- `expected 2264924160 to be greater than 2147483648`
- `expected 117440512 to be greater than 0`
- `expected 251658240 to be greater than 0`

## Impact

Specs that use `expect(value).to_be_greater_than(expected)` can report false
failures in at least the `std.spipe` matcher path used by `bin/simple run` and
`bin/simple test --mode=interpreter`.

## Workaround Used

The RISC-V FPGA memory-map specs now assert exact expected heap-start addresses
instead of using range comparison:

- Kria: `0x87000000` / `2264924160`
- LiteX: `0x4f000000` / `1325400064`

## Reproduction

Create a minimal SPipe spec that calls:

```spl
expect(117440512).to_be_greater_than(0)
```

Expected: pass.

Observed during the RISC-V FPGA verification session: false failure.

## Suspected Area

- `src/lib/nogc_sync_mut/spec.spl`
- `src/std/nogc_sync_mut/spec.spl`
- interpreter/runtime handling for comparison inside matcher methods
