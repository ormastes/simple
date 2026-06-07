# Ignored Return Specification

> <details>

<!-- sdn-diagram:id=ignored_return_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=ignored_return_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

ignored_return_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=ignored_return_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Ignored Return Specification

## Scenarios

### Ignored Return Value Lint

#### discarded return values

#### flags discarded return value from pure function (RET001)

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val code = "fn compute() -> i64:\n    42\n\nfn test():\n    compute()\n    print \"done\"\n"
val codes = check_ignored_return_text(code)
val has_ret001 = codes_contain(codes, "RET001")
expect(has_ret001).to_equal(true)
```

</details>

#### flags discarded string return

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val code = "fn get_name() -> text:\n    \"Alice\"\n\nfn test():\n    get_name()\n    print \"done\"\n"
val codes = check_ignored_return_text(code)
val has_ret001 = codes_contain(codes, "RET001")
expect(has_ret001).to_equal(true)
```

</details>

#### side-effectful functions

#### does not flag print calls

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val code = "fn test():\n    print \"hello\"\n    print \"world\"\n"
val codes = check_ignored_return_text(code)
val has_ret001 = codes_contain(codes, "RET001")
expect(has_ret001).to_equal(false)
```

</details>

#### does not flag push calls

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val code = "fn test():\n    var items: [text] = []\n    items.push(\"hello\")\n"
val codes = check_ignored_return_text(code)
val has_ret001 = codes_contain(codes, "RET001")
expect(has_ret001).to_equal(false)
```

</details>

#### implicit return (last expression)

#### does not flag last expression as implicit return

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val code = "fn compute() -> i64:\n    val x = 10\n    x * 2\n"
val codes = check_ignored_return_text(code)
val has_ret001 = codes_contain(codes, "RET001")
expect(has_ret001).to_equal(false)
```

</details>

#### does not flag last expression in function with return type

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val code = "fn greet(name: text) -> text:\n    \"Hello!\"\n"
val codes = check_ignored_return_text(code)
val has_ret001 = codes_contain(codes, "RET001")
expect(has_ret001).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/semantics/lint/ignored_return_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Ignored Return Value Lint

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
