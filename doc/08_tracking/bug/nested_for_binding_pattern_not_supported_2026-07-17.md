# Bug: canonical nested bare `for` binding pattern is not supported by bootstrap

- **Date:** 2026-07-17
- **Status:** open (source workaround in place; compiler fix not implemented)
- **Area:** bootstrap parser, HIR lowering, and interpreter for-loop pattern binding
- **Found by:** pure-Simple self-host/bootstrap source normalization
- **Parity guard:** `normalized_zip_enumerate` in `scripts/check/check-native-seed-parity.shs`

## Symptom

The canonical enumerate shorthand with a nested tuple item binding is not
supported end-to-end by the bootstrap pipeline:

```simple
fn main() -> i64:
    val left = [1, 2]
    val right = [10, 20]
    var total = 0
    for i, (a, b) in left.zip(right).enumerate():
        total = total + i + a + b
    print(total)
    return 0
```

The intended result is `34`. The canonical form either fails in the bootstrap
parser/HIR path or reaches for-loop execution without reliably binding the
nested `a`/`b` names. This is a language-support gap, not a zip or enumerate
semantic difference.

## Internal shape and affected layers

The shorthand is represented as an outer `(i, (a, b))` binding with automatic
enumeration. The bootstrap layers do not preserve and bind that nested pattern
consistently:

| Layer | Gap |
| --- | --- |
| Parser | The bare `i, pattern` shorthand and nested tuple pattern are not supported as one stable bootstrap AST binding shape. |
| HIR | For-loop tuple lowering extracts direct names but does not recursively lower the nested tuple binding. |
| Interpreter | The auto-enumerated `(index, item)` value is not reliably bound through the nested tuple pattern. |

## Current source normalization

Affected source uses the explicit equivalent shape instead of the canonical
shorthand:

```simple
for item in left.zip(right).enumerate():
    val (i, pair) = item
    val (a, b) = pair
```

This form is currently used in the variance/type-checking sources, including
`src/compiler/30.types/variance_types.spl`, `variance_phase6c.spl`, and
`variance_phase6d.spl`. The macro checker sources similarly use an explicit
`for pair in call.args.zip(...):` followed by `val (...) = pair` binding.

## Workaround and parity case

Keep the explicit two-step tuple destructuring until bootstrap support is
fixed. The selected parity case `normalized_zip_enumerate` is intended to
prove that this normalized `zip().enumerate()` shape produces `34` in both
seed and native modes. Run only that case with:

```sh
NATIVE_PARITY_CASES=normalized_zip_enumerate \
    sh scripts/check/check-native-seed-parity.shs
```

## Acceptance criteria

1. The canonical `for i, (a, b) in xs.zip(ys).enumerate():` form parses and
   checks through the bootstrap pipeline without source normalization.
2. Each iteration binds the index and both nested tuple elements to their
   actual values in bootstrap interpreter and native execution.
3. The canonical reproduction returns/prints `34`, and
   `normalized_zip_enumerate` remains a passing seed/native parity guard.
4. The affected compiler sources can be restored to the canonical shorthand
   without changing behavior or adding per-call-site destructuring workarounds.
