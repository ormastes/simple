# Range Step Specification

Ranges in Simple can be iterated with custom step values. This is primarily

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #RANGE-STEP |
| Category | Syntax |
| Status | Implemented |
| Source | `test/feature/usage/range_step_by_spec.spl` |
| Updated | 2026-04-07 |
| Generator | `simple sspec-docgen` (Rust) |

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 25 |
| Active scenarios | 25 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |

Ranges in Simple can be iterated with custom step values. This is primarily
used in slice syntax with the `[start:end:step]` notation, allowing iteration
over every Nth element or reversing sequences.

## Syntax

```simple
arr[::2]       # Every other element (step=2)
arr[1::2]      # Every other starting from index 1
arr[::-1]      # Reversed
arr[1:5:2]     # Slice from 1 to 5 with step 2

for i in (0..10).step_by(2):
print i    # 0, 2, 4, 6, 8
```

## Key Behaviors

- Step value can be positive (forward) or negative (reverse)
- Step of 1 is the default (every element)
- Step of -1 reverses the sequence
- Step of 2 selects every other element
- Works on arrays, strings, and any sliceable type

## Evidence

| Category | Count |
|----------|------:|
| Artifacts | 1 |

### Artifacts

| Item | Kind | Path |
|------|------|------|
| `result.json` | JSON artifact | `target/test-artifacts/feature/usage/range_step_by/result.json` |

## Scenarios

- selects every other element with step 2
- selects every third element with step 3
- selects every fourth element
- starts from index 1 with step 2
- starts from index 2 with step 3
- starts from middle of array
- slices range with step
- slices narrow range with step
- slices with step larger than range
- reverses entire array
- reverses empty array
- reverses single element
- reverses with step -2
- selects every other character
- reverses string
- selects odd-indexed characters
- slices string with step
- handles step equal to length
- handles step greater than length
- handles step of 1 (identity)
- handles empty slice with step
- extracts even indices
- extracts odd indices
- reverses for iteration
- samples at regular intervals
