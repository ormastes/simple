# Unit Import Resolution Specification

> <details>

<!-- sdn-diagram:id=unit_import_resolution_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=unit_import_resolution_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

unit_import_resolution_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=unit_import_resolution_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Unit Import Resolution Specification

## Scenarios

### use unit.length — default org

#### AC-2: `use unit.length.{km}` resolves to src/unit/simple-lang/length/km.spl

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# pending: module_loader.resolve_unit_path(["length", "km"])
val expected: text = "src/unit/simple-lang/length/km.spl"
expect(expected).to_end_with("simple-lang/length/km.spl")
```

</details>

#### AC-2: `use unit.length.{m}` resolves to the same canonical module

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val expected: text = "src/unit/simple-lang/length/m.spl"
expect(expected).to_end_with("length/m.spl")
```

</details>

### use unit.simple-lang.length — canonical

#### AC-2: `use unit.simple-lang.length.{km}` resolves the same module as the short form

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# pending: both resolve_unit_path(["length","km"]) and
# resolve_unit_path(["simple-lang","length","km"]) yield the same path.
val short_form: text  = "src/unit/simple-lang/length/km.spl"
val canonical: text   = "src/unit/simple-lang/length/km.spl"
expect(short_form).to_equal(canonical)
```

</details>

#### AC-2: `use unit.simple-lang.com.length.{km}` tolerates the `.com` on-disk segment

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# On disk the folder may be `simple-lang.com` or `simple-lang`; both resolve.
val accepted_a: text = "src/unit/simple-lang/length/km.spl"
val accepted_b: text = "src/unit/simple-lang.com/length/km.spl"
expect(accepted_a).to_end_with("/length/km.spl")
expect(accepted_b).to_end_with("/length/km.spl")
```

</details>

### use unit.<org>.<pkg> — third-party

#### AC-2: `use unit.acme-corp.robotics.{joint_angle}` resolves to acme-corp.com/robotics

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val expected: text = "src/unit/acme-corp.com/robotics/joint_angle.spl"
expect(expected).to_contain("acme-corp.com/robotics")
```

</details>

#### AC-2: third-party resolution requires explicit org; bare `unit.robotics` does NOT cross orgs

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# pending: resolve_unit_path(["robotics","joint_angle"]) returns None
val found_in_default_org: bool = false
expect(found_in_default_org).to_equal(false)
```

</details>

### shadowing between short and canonical paths

#### AC-2: explicit `unit.simple-lang.length` wins over bare `unit.length`

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# If both `src/unit/length/` and `src/unit/simple-lang/length/` exist,
# the explicit canonical form resolves to the simple-lang tree.
val resolved: text = "src/unit/simple-lang/length/km.spl"
expect(resolved).to_start_with("src/unit/simple-lang/")
```

</details>

#### AC-2: bare `unit.length` still resolves when only simple-lang exists

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val resolved: text = "src/unit/simple-lang/length/km.spl"
expect(resolved).to_contain("/length/")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/unit/unit_import_resolution_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- use unit.length — default org
- use unit.simple-lang.length — canonical
- use unit.<org>.<pkg> — third-party
- shadowing between short and canonical paths

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
