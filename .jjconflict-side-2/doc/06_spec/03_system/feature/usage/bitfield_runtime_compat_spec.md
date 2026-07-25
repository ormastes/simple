# Bitfield Runtime Compatibility

> Tests that real bitfield syntax is accepted and parsed correctly in the feature test path. Validates a basic bitfield declaration with a u8 backing type, including ready, mode, and reserved fields.

<!-- sdn-diagram:id=bitfield_runtime_compat_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=bitfield_runtime_compat_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

bitfield_runtime_compat_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=bitfield_runtime_compat_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Bitfield Runtime Compatibility

Tests that real bitfield syntax is accepted and parsed correctly in the feature test path. Validates a basic bitfield declaration with a u8 backing type, including ready, mode, and reserved fields.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Language Features |
| Status | In Progress |
| Source | `test/03_system/feature/usage/bitfield_runtime_compat_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests that real bitfield syntax is accepted and parsed correctly in the feature test path.
Validates a basic bitfield declaration with a u8 backing type, including ready, mode,
and reserved fields.

## Scenarios

### Bitfield Runtime Compatibility

#### accepts real bitfield syntax in feature test path

1. var flags: CompatFlags = CompatFlags new
   - Expected: flags.ready equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var flags: CompatFlags = CompatFlags.new(0)
expect(flags.ready).to_equal(0)
```

</details>

#### round-trips field writes through Flags.new packed runtime values

1. var f: Flags = Flags new
   - Expected: f.a equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var f: Flags = Flags.new(0)
f.a = 3
expect(f.a).to_equal(3)
```

</details>

#### preserves adjacent fields when writing one packed bitfield field

1. var f: Flags = Flags new
   - Expected: f.a equals `3`
   - Expected: f.b equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var f: Flags = Flags.new(0)
f.a = 3
f.b = 5
expect(f.a).to_equal(3)
expect(f.b).to_equal(5)
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
