# Driver Manifest Attr Specification

> 1. attr

<!-- sdn-diagram:id=driver_manifest_attr_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=driver_manifest_attr_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

driver_manifest_attr_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=driver_manifest_attr_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Driver Manifest Attr Specification

## Scenarios

### driver manifest attributes

#### parses positional @driver manifest fields

1. attr
2. ]) ?? default driver attr
   - Expected: parsed.kind equals `DriverManifestAttrKind.Driver`
   - Expected: parsed.driver_class equals `0`
   - Expected: parsed.vendor equals `0x8086`
   - Expected: parsed.device_ids.len() equals `2`
   - Expected: parsed.device_ids[0] equals `0x2922`
   - Expected: parsed.version equals `1.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val parsed = parse_driver_manifest_attrs([
    attr("driver", [int_expr(0), int_expr(0x8086), array_expr([int_expr(0x2922), int_expr(0x2829)]), string_expr("1.0")])
]) ?? default_driver_attr()
expect(parsed.kind).to_equal(DriverManifestAttrKind.Driver)
expect(parsed.driver_class).to_equal(0)
expect(parsed.vendor).to_equal(0x8086)
expect(parsed.device_ids.len()).to_equal(2)
expect(parsed.device_ids[0]).to_equal(0x2922)
expect(parsed.version).to_equal("1.0")
```

</details>

#### parses named @driver manifest fields

1. assign expr
2. assign expr
3. assign expr
4. assign expr
5. ]) ?? default driver attr
   - Expected: parsed.kind equals `DriverManifestAttrKind.Driver`
   - Expected: parsed.driver_class equals `8`
   - Expected: parsed.vendor equals `0x1234`
   - Expected: parsed.device_ids[1] equals `2`
   - Expected: parsed.version equals `2.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val parsed = parse_driver_manifest_attrs([
    attr("driver", [
        assign_expr("class", int_expr(8)),
        assign_expr("vendor", int_expr(0x1234)),
        assign_expr("device", array_expr([int_expr(1), int_expr(2)])),
        assign_expr("version", string_expr("2.0"))
    ])
]) ?? default_driver_attr()
expect(parsed.kind).to_equal(DriverManifestAttrKind.Driver)
expect(parsed.driver_class).to_equal(8)
expect(parsed.vendor).to_equal(0x1234)
expect(parsed.device_ids[1]).to_equal(2)
expect(parsed.version).to_equal("2.0")
```

</details>

#### parses named @native_lib manifest fields

1. assign expr
2. assign expr
3. ]) ?? default driver attr
   - Expected: parsed.kind equals `DriverManifestAttrKind.NativeLib`
   - Expected: parsed.driver_class equals `15`
   - Expected: parsed.abi equals `simple`
   - Expected: parsed.version equals `12.3`
   - Expected: parsed.device_ids.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val parsed = parse_driver_manifest_attrs([
    attr("native_lib", [
        assign_expr("abi", string_expr("simple")),
        assign_expr("version", string_expr("12.3"))
    ])
]) ?? default_driver_attr()
expect(parsed.kind).to_equal(DriverManifestAttrKind.NativeLib)
expect(parsed.driver_class).to_equal(15)
expect(parsed.abi).to_equal("simple")
expect(parsed.version).to_equal("12.3")
expect(parsed.device_ids.len()).to_equal(0)
```

</details>

#### returns nil when no driver manifest attribute exists

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(parse_driver_manifest_attrs([attr("repr", [string_expr("C")])])).to_be_nil()
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/common/driver_manifest_attr_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- driver manifest attributes

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
