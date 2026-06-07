# Print Log Policy Specification

> <details>

<!-- sdn-diagram:id=print_log_policy_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=print_log_policy_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

print_log_policy_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=print_log_policy_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Print Log Policy Specification

## Scenarios

### print log policy source wiring

#### routes non-script print diagnostics through LOG001

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val parser = rt_file_read_text("src/compiler/10.frontend/core/parser.spl") ?? ""
expect(parser.contains("fn parser_warn_print_if_needed")).to_equal(true)
expect(parser.contains("parser_path_is_script(module_get_path())")).to_equal(true)
expect(parser.contains("LOG001: use log() instead of print() in non-script code")).to_equal(true)
```

</details>

#### checks bare print statements and module-level print declarations

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val stmts = rt_file_read_text("src/compiler/10.frontend/core/parser_stmts.spl") ?? ""
val decls = rt_file_read_text("src/compiler/10.frontend/core/parser_decls_part2.spl") ?? ""
expect(stmts.contains("if par_text_get() == \"print\":")).to_equal(true)
expect(stmts.contains("parser_warn_print_if_needed()")).to_equal(true)
expect(decls.contains("elif par_text_get() == \"print\":")).to_equal(true)
expect(decls.contains("parser_warn_print_if_needed()")).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/parser/print_log_policy_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- print log policy source wiring

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
