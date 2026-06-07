# DE10-Nano Quartus Setup Guide Specification

> Verifies AC-4: the Quartus Prime Lite setup guide for DE10-Nano exists and contains the required version, device, and workflow information. Tests that the guide helper module returns the correct constants.

<!-- sdn-diagram:id=de10nano_quartus_setup_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=de10nano_quartus_setup_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

de10nano_quartus_setup_spec -> std
de10nano_quartus_setup_spec -> doc
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=de10nano_quartus_setup_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 11 | 11 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# DE10-Nano Quartus Setup Guide Specification

Verifies AC-4: the Quartus Prime Lite setup guide for DE10-Nano exists and contains the required version, device, and workflow information. Tests that the guide helper module returns the correct constants.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | opensource-riscv-rtl-simpleos |
| Category | Infrastructure |
| Difficulty | 1/5 |
| Status | Draft |
| Requirements | REQ-4 |
| Source | `test/01_unit/doc/de10nano_quartus_setup_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Verifies AC-4: the Quartus Prime Lite setup guide for DE10-Nano exists
and contains the required version, device, and workflow information.
Tests that the guide helper module returns the correct constants.

Covers:
- AC-4 (Cyclone V / Quartus setup guide documented for DE10-Nano)

## Scenarios

### DE10-Nano Quartus Setup Guide

#### AC-4: guide content is non-empty

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val g = guide()
val len = g.length()
expect(len).to_be_greater_than(0)
```

</details>

#### AC-4: guide contains Quartus Prime version reference

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val g = guide()
expect(g).to_contain("Quartus")
```

</details>

#### AC-4: guide contains device string 5CSEBA6U23I7

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val g = guide()
expect(g).to_contain("5CSEBA6U23I7")
```

</details>

#### AC-4: guide contains DE10-Nano board name

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val g = guide()
expect(g).to_contain("DE10-Nano")
```

</details>

#### AC-4: guide contains LiteX de10nano target

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val g = guide()
expect(g).to_contain("de10nano")
```

</details>

#### AC-4: guide contains download or install step

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val g = guide()
expect(g).to_contain("install")
```

</details>

#### AC-4: guide contains VexRiscv or SMP reference

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val g = guide()
expect(g).to_contain("VexRiscv")
```

</details>

### Quartus setup guide constants

#### AC-4: quartus_lite_version is non-empty

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val v = quartus_lite_version()
val len = v.length()
expect(len).to_be_greater_than(0)
```

</details>

#### AC-4: de10nano_device_string is 5CSEBA6U23I7

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val d = de10nano_device_string()
expect(d).to_equal("5CSEBA6U23I7")
```

</details>

#### AC-4: litex_de10nano_build_command contains make.py

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cmd = litex_de10nano_build_command()
expect(cmd).to_contain("make.py")
```

</details>

#### AC-4: litex_de10nano_build_command contains de10nano

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cmd = litex_de10nano_build_command()
expect(cmd).to_contain("de10nano")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 11 |
| Active scenarios | 11 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Requirements:** [REQ-4](REQ-4)


</details>
