# Test runner thresholds lose signs and accept f64 overflow

- **Date:** 2026-10-28
- **Status:** Fixed in this change
- **Severity:** Medium — runner resource safeguards can use a threshold different from the requested value
- **Component:** `src/lib/nogc_sync_mut/test_runner/test_runner_args.spl`

## Reproduction

The runner accepts signed decimal values for `--cpu-threshold` and
`--mem-threshold`, but its old parser discarded the sign and did not place
fractional digits by their decimal position:

```text
--cpu-threshold -0.5  -> +0.5
--mem-threshold -2.75 -> +2.12
```

It also accepted a 400-digit decimal in `test_args_validation_error` even
though conversion overflowed to infinity. An infinite threshold prevents the
corresponding `system_exceeds_threshold` comparison from firing.

## Root cause and fix

`parse_f64` accumulated fractional digits as an integer sum, then divided by
the number of digits; it never applied the leading minus sign. The validator
checked only that a signed value began with a digit or dot, so malformed
characters and values outside finite f64 range could pass.

The parser now applies sign after decimal accumulation and places each
fractional digit correctly. The validator accepts only decimal syntax, rejects
non-finite conversions in both separated and `=` forms, and retains its
existing missing-value errors. Negative values remain valid: the system
monitor unit spec intentionally uses `-1.0` as a force-violation threshold and
`101.0` as a safe threshold.

`parse_test_args` is a low-level conversion routine; the CLI validates with
`test_args_validation_error` before calling it. The scoped SDoctest client
route was the exception: it dispatched before the general validation block.
It now validates inside that route before parsing or running documentation.

## Evidence

On Phase1 aa58, before the fix the focused regression spec failed two cases:
`-0.5` became `+0.5`, and `-2.75` became `+2.12`. A 400-digit value also passed
validation. After the fix, the focused spec passes 9/9 examples, covering
negative, positive, zero, separated and `=` forms, malformed syntax,
missing values before another flag, and positive and negative f64 overflow.
The scoped SDoctest route regression was red before the gate fix and now passes
1/1, confirming malformed threshold input is rejected before the route runs.
