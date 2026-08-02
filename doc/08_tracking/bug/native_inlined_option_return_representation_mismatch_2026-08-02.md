# Native inlined Option return representation mismatch

Status: open  
Severity: P1 native semantic parity  
Fix owner: `/root/native-option-return-representation` — TRACKED, NOT PARALLEL-CLAIMABLE

## Reproduction

A no-stub pure-Simple Stage 3 build of the async database probe links and runs,
but this comparison returns false for a row that contains the requested ID:

```simple
row.get("run_id") == Some(run_id)
```

Disassembly shows the inlined `SdnRow.get` result as a bare text handle while
`Some(run_id)` is constructed with `rt_enum_new`. `rt_native_eq` therefore
compares two different physical representations.

The same probe also showed that printing the raw result of `text.starts_with`
passes an unboxed runtime `i64` boolean to `rt_println_value`, which renders as
`nil`; branching on the predicate remains the correct discriminator. That bool
boxing defect is already covered by the native MC/DC work and is not duplicated
here.

## Bounded mitigation result

An explicit nil check plus unwrap was tested and rejected: the pure-Simple
native probe still returned false. The consumer workaround was removed rather
than committing an ineffective divergence; the seed/interpreter behavior stays
covered by the existing database regression.

## Compiler repair required

Native lowering must keep function-returned and inlined `Option<T>` values in
one canonical representation across calls, inlining, equality, pattern
matching, `??`, `?`, and `unwrap`. Add positive/negative focused probes for
text and one non-text payload before changing the representation.
