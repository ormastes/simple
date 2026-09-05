# math_bridge_import_name_drift_class_spec

> Defect-CLASS spec: an office module importing a stdlib name that does not exist.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# math_bridge_import_name_drift_class_spec

Defect-CLASS spec: an office module importing a stdlib name that does not exist.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/office/sheets/math_bridge_import_name_drift_class_spec.spl` |
| Updated | 2026-08-18 |
| Generator | `simple spipe-docgen` (Simple) |

Defect-CLASS spec: an office module importing a stdlib name that does not exist.

The `variance_sample` defect was one instance of a class this repo has hit more
than once (the same session found `ed25519_verify` imported under a name the
SFFI wrapper never exported). The failure mode is nasty because it is not a
wrong answer: the importing module fails to resolve, so EVERY function in it
becomes unreachable at once, and a caller that never touches the drifted symbol
still breaks.

There is no reflection here, so the check is direct: name every symbol
`math_bridge.spl` imports from the pure-math stdlib modules and call it once.
A drifted name cannot survive this spec loading.

POSITIVE CONTROL: `_control_sees_a_real_import` asserts the imported symbols
actually compute — a spec that only imported names could pass while every value
was garbage, and a spec whose subject module silently vanished would report a
clean sweep for the wrong reason.

## Scenarios

### office math_bridge: stdlib import names must resolve

#### every statistics symbol math_bridge imports is callable

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_close(mean(_vals()), 5.0)).to_equal(true)
expect(_close(median(_vals()), 5.0)).to_equal(true)
expect(_close(var_sample(_vals()), 10.0 / 3.0)).to_equal(true)
expect(_close(var_pop(_vals()), 2.5)).to_equal(true)
expect(_close(stdev_sample(_vals()) * stdev_sample(_vals()), 10.0 / 3.0)).to_equal(true)
expect(_close(stdev_pop(_vals()) * stdev_pop(_vals()), 2.5)).to_equal(true)
expect(_close(standardize(7.0, 5.0, 2.0), 1.0)).to_equal(true)
```

</details>

#### every special-math symbol math_bridge imports is callable

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_close(sqrt_f64(9.0), 3.0)).to_equal(true)
expect(_close(exp_f64(0.0), 1.0)).to_equal(true)
expect(_close(ln_f64(1.0), 0.0)).to_equal(true)
```

</details>

#### _control_sees_a_real_import: the bridge itself resolves and delegates

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_close(excel_var(_vals()), var_sample(_vals()))).to_equal(true)
expect(_close(excel_sqrt(9.0), 3.0)).to_equal(true)
expect(_close(excel_exp(0.0), 1.0)).to_equal(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
