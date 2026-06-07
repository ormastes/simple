# CompilerProfile Enum Specification

> Tests for CompilerProfile enum — round-trip text conversion and alias handling. These are pure logic tests that work in interpreter mode.

<!-- sdn-diagram:id=compiler_profile_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=compiler_profile_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

compiler_profile_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=compiler_profile_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 16 | 16 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# CompilerProfile Enum Specification

Tests for CompilerProfile enum — round-trip text conversion and alias handling. These are pure logic tests that work in interpreter mode.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Infrastructure |
| Status | Implemented |
| Source | `test/01_unit/compiler/config/compiler_profile_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests for CompilerProfile enum — round-trip text conversion and alias handling.
These are pure logic tests that work in interpreter mode.

## Scenarios

### CompilerProfile

#### to_text

#### converts Dev to text

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val profile = CompilerProfile.Dev
expect(profile.to_text()).to_equal("dev")
```

</details>

#### converts Test to text

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val profile = CompilerProfile.Test
expect(profile.to_text()).to_equal("test")
```

</details>

#### converts Prod to text

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val profile = CompilerProfile.Prod
expect(profile.to_text()).to_equal("prod")
```

</details>

#### converts Sdn to text

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val profile = CompilerProfile.Sdn
expect(profile.to_text()).to_equal("sdn")
```

</details>

#### from_text

#### parses dev

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val profile = CompilerProfile.from_text("dev")
expect(profile.to_text()).to_equal("dev")
```

</details>

#### parses development alias

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val profile = CompilerProfile.from_text("development")
expect(profile.to_text()).to_equal("dev")
```

</details>

#### parses test

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val profile = CompilerProfile.from_text("test")
expect(profile.to_text()).to_equal("test")
```

</details>

#### parses testing alias

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val profile = CompilerProfile.from_text("testing")
expect(profile.to_text()).to_equal("test")
```

</details>

#### parses prod

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val profile = CompilerProfile.from_text("prod")
expect(profile.to_text()).to_equal("prod")
```

</details>

#### parses production alias

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val profile = CompilerProfile.from_text("production")
expect(profile.to_text()).to_equal("prod")
```

</details>

#### parses release alias

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val profile = CompilerProfile.from_text("release")
expect(profile.to_text()).to_equal("prod")
```

</details>

#### parses sdn

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val profile = CompilerProfile.from_text("sdn")
expect(profile.to_text()).to_equal("sdn")
```

</details>

#### parses data alias

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val profile = CompilerProfile.from_text("data")
expect(profile.to_text()).to_equal("sdn")
```

</details>

#### defaults unknown to Dev

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val profile = CompilerProfile.from_text("garbage")
expect(profile.to_text()).to_equal("dev")
```

</details>

#### round-trip

#### Dev round-trips through text

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val original = CompilerProfile.Dev
val restored = CompilerProfile.from_text(original.to_text())
expect(restored.to_text()).to_equal("dev")
```

</details>

#### Prod round-trips through text

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val original = CompilerProfile.Prod
val restored = CompilerProfile.from_text(original.to_text())
expect(restored.to_text()).to_equal("prod")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 16 |
| Active scenarios | 16 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
