# Cli Specification

> <details>

<!-- sdn-diagram:id=cli_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=cli_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

cli_spec -> std
cli_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=cli_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 17 | 17 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Cli Specification

## Scenarios

### SimpleOS CLI parser

#### rejects a trailing bare --log flag

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(handle_os(["build", "--log"])).to_equal(1)
```

</details>

#### rejects an empty inline --log value

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(handle_os(["build", "--log="])).to_equal(1)
```

</details>

#### rejects bare --log followed by another option

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(handle_os(["build", "--log", "--arch=x86_64"])).to_equal(1)
```

</details>

#### rejects typoed --log-prefixed flags

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(handle_os(["build", "--logg", "off"])).to_equal(1)
```

</details>

#### rejects a single invalid inline --log value

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(handle_os(["build", "--log=maybe"])).to_equal(1)
```

</details>

#### rejects an invalid later --log value instead of keeping an earlier valid one

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(handle_os(["build", "--log=on", "--log", "maybe"])).to_equal(1)
```

</details>

#### rejects a trailing bare --arch flag

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(handle_os(["build", "--arch"])).to_equal(1)
```

</details>

#### rejects bare --arch followed by another option

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(handle_os(["build", "--arch", "--log=off"])).to_equal(1)
```

</details>

#### rejects a trailing bare --target flag

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(handle_os(["build", "--target"])).to_equal(1)
```

</details>

#### rejects bare --target followed by another option

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(handle_os(["build", "--target", "--log=off"])).to_equal(1)
```

</details>

#### rejects a trailing bare --scenario flag

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(handle_os(["build", "--scenario"])).to_equal(1)
```

</details>

#### rejects bare --scenario followed by another option

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(handle_os(["build", "--scenario", "--arch=x86_64"])).to_equal(1)
```

</details>

#### rejects a trailing bare --board flag

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(handle_os(["test", "--board"])).to_equal(1)
```

</details>

#### rejects bare --board followed by another option

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(handle_os(["test", "--board", "--arch=riscv64"])).to_equal(1)
```

</details>

#### rejects unsupported board names

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(handle_os(["test", "--board=arm32"])).to_equal(1)
```

</details>

#### rejects unsupported x86 alias board names

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(handle_os(["test", "--board=x86"])).to_equal(1)
```

</details>

#### restores SIMPLE_OS_LOG_MODE after a failed canonical build path

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val prior = rt_env_get("SIMPLE_OS_LOG_MODE") ?? ""
expect(handle_os(["build", "--log=off", "--arch=bogus"])).to_equal(1)
expect(rt_env_get("SIMPLE_OS_LOG_MODE") ?? "").to_equal(prior)
expect(rt_env_set("SIMPLE_OS_LOG_MODE", prior)).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/cli_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- SimpleOS CLI parser

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 17 |
| Active scenarios | 17 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
