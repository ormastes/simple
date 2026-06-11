# Exhaustiveness Validator Specification

> <details>

<!-- sdn-diagram:id=exhaustiveness_validator_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=exhaustiveness_validator_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

exhaustiveness_validator_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=exhaustiveness_validator_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Exhaustiveness Validator Specification

## Scenarios

### Exhaustiveness Validator

#### detects catch-all lines and ignores comment-only mentions

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val subject = validator()

expect(subject.is_catch_all_line("_ => panic!(\"unsupported\")")).to_be(true)
expect(subject.is_catch_all_line("    foo _ => bar")).to_be(true)
expect(subject.is_catch_all_line("// _ => documented example")).to_be(false)
```

</details>

#### only treats explicit documentation as intentional

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val subject = validator()

expect(subject.is_intentional_catch_all("// Intentional catch-all for type matching")).to_be(true)
expect(subject.is_intentional_catch_all("// Type matching only for metadata")).to_be(true)
expect(subject.is_intentional_catch_all("// Other instructions not yet implemented")).to_be(false)
```

</details>

#### keeps undispatched MirInst catch-alls as errors

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val subject = validator()
val context = "match inst {\n    MirInst::Foo => handle_foo(),\n    _ => todo!(\"later\")\n}"

expect(subject.determine_severity("backend.rs", context, false)).to_equal(CatchAllSeverity.Error)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/backend/exhaustiveness_validator_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Exhaustiveness Validator

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
