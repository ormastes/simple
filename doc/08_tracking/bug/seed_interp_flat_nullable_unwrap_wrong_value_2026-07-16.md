# seed_interp: flat-nullable `.unwrap()` returns wrong value

- Status: open
- Component: Rust seed interpreter (`bin/simple run`, SIMPLE_BOOTSTRAP unset)
- Severity: medium (oracle landmine — corrupts oracle-vs-native parity comparisons)
- Found: 2026-07-16 during repro-verification of `native_text_option_unwrap_pointer_value_2026-07-15`

## Symptom

Flat-nullable optional values (declared as `T?` and assigned a bare value) misunwrap when using `.unwrap()`:

```spl
fn main():
    val n: i64? = 100
    print(n.unwrap())
    
    val t: text? = "opt"
    print(t.unwrap())
    
    val explicit = Some(9)
    print(explicit.unwrap())
```

Observed output:
```
3
<empty line>
9
```

Expected output:
```
100
opt
9
```

Control: explicit `Some(9).unwrap()` correctly prints `9`, proving the `.unwrap()` path for explicitly-constructed Some values is correct. Only the **flat nullable form** (`val x: T? = value` assigned a bare value, not wrapped in Some) mis-unwraps.

## Details

- **i64? case:** `val n: i64? = 100; n.unwrap()` prints `3` instead of `100`. The value `3` is consistent with the seed's known BoxInt tag/shift landmine class (see cross-reference: `doc/08_tracking/bug/` docs mentioning `box_int` or `tag-box`).
- **text? case:** `val t: text? = "opt"; t.unwrap()` prints an empty line instead of `"opt"`.
- **nil case:** `val x: i64? = nil; x.unwrap()` still panics correctly (behavior expected, not verified for this bug).
- **Workaround:** Use explicit `Some(value)` construction instead of flat-nullable assignment, or document explicit expected values in harness tests and compare against those instead of the oracle.

## Impact on parity harness

Any test case using flat-nullable optional values with `.unwrap()` cannot trust the oracle for comparison. The seed's output is corrupted and will produce false negatives (correct native code marked as wrong due to oracle corruption) or cause the harness to skip/annotate the case.

Examples of affected patterns:
- `val result: MyType? = compute_value(); val x = result.unwrap()`
- `filter()` / `map()` chains that unwrap optional field extraction

## Root cause hypothesis

Seed interpreter representation mismatch for flat-nullable optionals at the `.unwrap()` call site. Unlike explicit `Some(value)`, the flat form may store the value using a different tagged representation (possibly a BoxInt wrapper as evidenced by the i64→3 corruption pattern). The `.unwrap()` method in the seed may not account for this alternate representation.

Precedent: seed's known flat-Option representation bugs (see `native_text_option_unwrap_pointer_value_2026-07-15.md`, which this bug was discovered while verifying).

## Next steps

1. Seed-side investigation: inspect seed interpreter flat-optional construction and `.unwrap()` method dispatch in `interpreter_value.rs` / `runtime/src/value/option.rs`.
2. Do NOT apply native-side workarounds (e.g., special-casing `.unwrap()` calls in parity harness). This bug is a seed defect; working around it hides the root cause.
3. When the seed is next rebuilt (post-native-build campaign), verify the flat-nullable `.unwrap()` path against these test cases.

## Workaround (oracle-side)

For parity test cases requiring Optional `.unwrap()` semantics:
- Replace `val x: T? = value; x.unwrap()` with `val x = Some(value); x.unwrap()`
- Or pre-compute and document the expected value, comparing native output against it rather than the oracle

## Not a native path bug

Native-build's handling of flat-nullable `.unwrap()` is correct (verified by `native_text_option_unwrap_pointer_value_2026-07-15.md` which shows native prints `"opt"` as expected). This is a seed-only (Rust interpreter) defect.
