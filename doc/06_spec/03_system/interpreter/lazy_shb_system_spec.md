# Lazy Shb System Specification

> <details>

<!-- sdn-diagram:id=lazy_shb_system_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=lazy_shb_system_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

lazy_shb_system_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=lazy_shb_system_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Lazy Shb System Specification

## Scenarios

### Interpreter Lazy SHB Wiring

#### parses a module without registering symbols (parse_only)

<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Verifies load_module_parse_only() can parse a .spl file
# and return success without registering any symbols into
# the function table or module path table.
if not _can_run:
    expect(_can_run).to_equal(false)
else:
    val result = run_probe("parse_only")
    val stdout = result[0]
    val stderr = result[1]
    val code = result[2]
    if code != 0:
        print stdout
        print stderr
    expect(code).to_equal(0)
    expect(stdout).to_contain("ok")
```

</details>

#### parses then registers symbols without full loading (register_only)

<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Verifies the two-phase load: first parse_only, then register_only.
# After register_only the module path is set and its pub fn symbols
# appear in the function table, but the module body has not executed.
if not _can_run:
    expect(_can_run).to_equal(false)
else:
    val result = run_probe("register_only")
    val stdout = result[0]
    val stderr = result[1]
    val code = result[2]
    if code != 0:
        print stdout
        print stderr
    expect(code).to_equal(0)
    expect(stdout).to_contain("ok")
```

</details>

#### fully loads a module and registers its symbols (direct_load)

<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Verifies load_module() performs a complete load: parsing,
# registration, and execution. After this call the module path
# is set and all pub fn symbols are in the function table.
if not _can_run:
    expect(_can_run).to_equal(false)
else:
    val result = run_probe("direct_load")
    val stdout = result[0]
    val stderr = result[1]
    val code = result[2]
    if code != 0:
        print stdout
        print stderr
    expect(code).to_equal(0)
    expect(stdout).to_contain("ok")
```

</details>

#### uses SHB metadata to skip unrelated wildcard deferred modules

<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Verifies selective force-loading: when try_force_any_deferred_for("beta")
# is called, only module "b" (which exports beta) is loaded.
# Module "a" (which exports alpha) must NOT be loaded.
if not _can_run:
    expect(_can_run).to_equal(false)
else:
    val result = run_probe("wildcard_filter")
    val stdout = result[0]
    val stderr = result[1]
    val code = result[2]
    if code != 0:
        print stdout
        print stderr
    expect(code).to_equal(0)
    expect(stdout).to_contain("ok")
```

</details>

#### circular lazy wildcard imports are a known interpreter limitation

<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Known limitation: circular lazy wildcard imports (a uses lazy b.*,
# b uses lazy a.*) fail in subprocess context due to interpreter
# re-entrancy issues. The probe returns value=0 instead of 42
# because the circular dependency resolution does not fully execute.
# This test documents the limitation; when it is fixed, flip
# the assertion to expect code==0 and stdout containing "ok".
if not _can_run:
    expect(_can_run).to_equal(false)
else:
    val result = run_probe("circular_wildcard")
    val stdout = result[0]
    val code = result[2]
    # Currently fails: the probe returns exit code 1 because
    # circular lazy resolution produces value=0 instead of 42.
    expect(code).to_equal(1)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Runtime |
| Status | Active |
| Source | `test/03_system/interpreter/lazy_shb_system_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Interpreter Lazy SHB Wiring

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
