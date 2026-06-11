# Jit Specification

> <details>

<!-- sdn-diagram:id=jit_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=jit_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

jit_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=jit_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Jit Specification

## Scenarios

### Jit

#### keeps file-backed JIT state lifecycle available

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = jit_source()

expect(source).to_contain("class JitState:")
expect(source).to_contain("fn _state_path() -> text")
expect(source).to_contain("fn _load_state() -> JitState")
expect(source).to_contain("fn _save_state(s: JitState)")
expect(source).to_contain("fn jit_init(threshold: i64, verbose: i64)")
expect(source).to_contain("fn jit_cleanup()")
```

</details>

#### keeps JIT call tracking and threshold APIs available

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = jit_source()

expect(source).to_contain("fn jit_record_call(fn_name: text)")
expect(source).to_contain("fn jit_get_call_count(fn_name: text) -> i64")
expect(source).to_contain("fn jit_should_compile(fn_name: text) -> bool")
expect(source).to_contain("jit_get_call_count(fn_name) >= s.threshold")
expect(source).to_contain("fn jit_total_tracked() -> i64")
```

</details>

#### keeps JIT compilation status APIs available

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = jit_source()

expect(source).to_contain("fn jit_is_compiled(fn_name: text) -> bool")
expect(source).to_contain("fn jit_mark_compiled(fn_name: text)")
expect(source).to_contain("fn jit_try_compile(fn_name: text, mir_data: text) -> bool")
expect(source).to_contain("fn jit_try_execute(fn_name: text, args: [i64]) -> i64")
expect(source).to_contain("fn jit_compiled_count() -> i64")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler_core/interpreter/jit_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Jit

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
