# Closure Capture Specification

> <details>

<!-- sdn-diagram:id=closure_capture_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=closure_capture_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

closure_capture_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=closure_capture_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Closure Capture Specification

## Scenarios

### Closure Capture Lint

#### closure modifying outer variable

#### flags nested fn that modifies an outer var (CLOS001)

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val code = "fn compute():\n    var counter = 0\n    fn inc():\n        counter = counter + 1\n    inc()\n"
val codes = check_closure_capture_text(code)
val has_clos001 = codes_contain(codes, "CLOS001")
expect(has_clos001).to_equal(true)
```

</details>

#### flags nested fn that reassigns outer var

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val code = "fn test():\n    var x = 10\n    fn update():\n        x = 42\n    update()\n"
val codes = check_closure_capture_text(code)
val has_clos001 = codes_contain(codes, "CLOS001")
expect(has_clos001).to_equal(true)
```

</details>

#### closure reading outer variable

#### does not flag nested fn that only reads outer var

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val code = "fn compute() -> i64:\n    val x = 10\n    fn double() -> i64:\n        x * 2\n    double()\n"
val codes = check_closure_capture_text(code)
val has_clos001 = codes_contain(codes, "CLOS001")
expect(has_clos001).to_equal(false)
```

</details>

#### does not flag nested fn reading outer val

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val code = "fn greet():\n    val name = \"Alice\"\n    fn say():\n        print \"Hello\"\n    say()\n"
val codes = check_closure_capture_text(code)
val has_clos001 = codes_contain(codes, "CLOS001")
expect(has_clos001).to_equal(false)
```

</details>

#### module-level var mutation

#### does not flag module-level var mutation

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val code = "var global_count = 0\n\nfn increment():\n    global_count = global_count + 1\n"
val codes = check_closure_capture_text(code)
val has_clos001 = codes_contain(codes, "CLOS001")
expect(has_clos001).to_equal(false)
```

</details>

#### does not flag module-level var push

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val code = "var items: [text] = []\n\nfn add_item(item: text):\n    items.push(item)\n"
val codes = check_closure_capture_text(code)
val has_clos001 = codes_contain(codes, "CLOS001")
expect(has_clos001).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/semantics/lint/closure_capture_spec.spl` |
| Updated | 2026-07-06 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Closure Capture Lint

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
