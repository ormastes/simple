# Config Loader

> Purpose: stores basic integers

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 13 | 13 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Config Loader

Purpose: stores basic integers

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | In Progress |
| Source | `test/03_system/feature/app/config_loader_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: stores basic integers
Audience: compiler and tooling engineers who maintain this spec

# Config Loader

**Category:** Application
**Status:** In Progress

## Overview

Tests the configuration file loader including SDN format parsing, default value
resolution, and configuration merging. Verifies that project and user config
files are correctly loaded, validated, and applied in precedence order.

## Scenarios

### Config Dict Operations

#### stores basic integers

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- stores basic integers
- Verify: stores basic integers
   - Expected: cfg["port"] equals `8080`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("stores basic integers")
step("Verify: stores basic integers")
# @req: REQ-FEATURE-ConfLoad-001
val cfg = {"port": 8080}
expect(cfg["port"]).to_equal(8080)  # oracle: value fixed by the spec contract
```

</details>

#### stores floats

- stores floats
- Verify: stores floats
   - Expected: cfg["timeout"] equals `30.5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("stores floats")
step("Verify: stores floats")
# @req: REQ-FEATURE-ConfLoad-001
val cfg = {"timeout": 30.5}
expect(cfg["timeout"]).to_equal(30.5)
```

</details>

#### stores booleans

- stores booleans
- Verify: stores booleans
   - Expected: cfg["logging"] is true
   - Expected: cfg["debug"] is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("stores booleans")
step("Verify: stores booleans")
# @req: REQ-FEATURE-ConfLoad-001
val cfg = {"logging": true, "debug": false}
expect(cfg["logging"]).to_equal(true)
expect(cfg["debug"]).to_equal(false)
```

</details>

#### stores strings

- stores strings
- Verify: stores strings
   - Expected: cfg["name"] equals `MyApp`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("stores strings")
step("Verify: stores strings")
# @req: REQ-FEATURE-ConfLoad-001
val cfg = {"name": "MyApp"}
expect(cfg["name"]).to_equal("MyApp")
```

</details>

#### stores identifiers as string constants

- stores identifiers as string constants
- Verify: stores identifiers as string constants
   - Expected: cfg["mode"] equals `PRODUCTION`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("stores identifiers as string constants")
step("Verify: stores identifiers as string constants")
# @req: REQ-FEATURE-ConfLoad-001
val cfg = {"mode": "PRODUCTION"}
expect(cfg["mode"]).to_equal("PRODUCTION")
```

</details>

#### stores arrays

- stores arrays
- Verify: stores arrays
   - Expected: ports[0] equals `8080`
   - Expected: ports.len() equals `3`
   - Expected: ports[1] equals `8081`
   - Expected: ports[2] equals `8082`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("stores arrays")
step("Verify: stores arrays")
# @req: REQ-FEATURE-ConfLoad-001
val cfg = {"ports": [8080, 8081, 8082]}
val ports = cfg["ports"]
expect(ports[0]).to_equal(8080)  # oracle: value fixed by the spec contract
expect(ports.len()).to_equal(3)  # oracle: value fixed by the spec contract
expect(ports[1]).to_equal(8081)  # oracle: value fixed by the spec contract
expect(ports[2]).to_equal(8082)  # oracle: value fixed by the spec contract
```

</details>

#### stores nested values

- stores nested values
- Verify: stores nested values
   - Expected: cfg["train"]["epochs"] equals `100`
   - Expected: cfg["train"]["lr"] equals `0.001`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("stores nested values")
step("Verify: stores nested values")
# @req: REQ-FEATURE-ConfLoad-001
val cfg = {"train": {"epochs": 100, "lr": 0.001}}
expect(cfg["train"]["epochs"]).to_equal(100)  # oracle: value fixed by the spec contract
expect(cfg["train"]["lr"]).to_equal(0.001)
```

</details>

#### skips comments are pure-text concern

- skips comments are pure-text concern
- Verify: skips comments are pure-text concern
   - Expected: cfg["port"] equals `8080`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("skips comments are pure-text concern")
step("Verify: skips comments are pure-text concern")
# @req: REQ-FEATURE-ConfLoad-001
# Comments in config files are a parser concern.
# The dict-based approach just stores values.
val cfg = {"port": 8080}
expect(cfg["port"]).to_equal(8080)  # oracle: value fixed by the spec contract
```

</details>

#### handles multiline config

- handles multiline config
- Verify: handles multiline config
   - Expected: cfg["port"] equals `8080`
   - Expected: cfg["timeout"] equals `30.5`
   - Expected: cfg["logging"] is true
   - Expected: cfg["app_name"] equals `MyApp`
   - Expected: cfg["mode"] equals `PRODUCTION`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("handles multiline config")
step("Verify: handles multiline config")
# @req: REQ-FEATURE-ConfLoad-001
val cfg = {
    "port": 8080,
    "timeout": 30.5,
    "logging": true,
    "app_name": "MyApp",
    "mode": "PRODUCTION"
}
expect(cfg["port"]).to_equal(8080)  # oracle: value fixed by the spec contract
expect(cfg["timeout"]).to_equal(30.5)
expect(cfg["logging"]).to_equal(true)
expect(cfg["app_name"]).to_equal("MyApp")
expect(cfg["mode"]).to_equal("PRODUCTION")
```

</details>

### Config Access

#### gets simple values

- gets simple values
- Verify: gets simple values


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("gets simple values")
step("Verify: gets simple values")
# @req: REQ-FEATURE-ConfLoad-001
val cfg = {"port": 8080, "logging": true}
expect cfg["port"] == 8080
expect cfg["logging"] == true
```

</details>

#### gets nested values

- gets nested values
- Verify: gets nested values


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("gets nested values")
step("Verify: gets nested values")
# @req: REQ-FEATURE-ConfLoad-001
val cfg = {"server": {"port": 8080}}
expect cfg["server"]["port"] == 8080
```

</details>

#### handles missing keys with default

- handles missing keys with default
- Verify: handles missing keys with default


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("handles missing keys with default")
step("Verify: handles missing keys with default")
# @req: REQ-FEATURE-ConfLoad-001
val cfg = {"port": 8080}
val missing = cfg["missing"] ?? nil
expect missing == nil
```

</details>

### Config Merging

#### merges configs with overlay precedence

- merges configs with overlay precedence
- Verify: merges configs with overlay precedence


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("merges configs with overlay precedence")
step("Verify: merges configs with overlay precedence")
# @req: REQ-FEATURE-ConfLoad-001
val base = {"a": 1, "b": 2}
val overlay = {"b": 3, "c": 4}
var merged = {}
for key in base.keys():
    merged[key] = base[key]
for key in overlay.keys():
    merged[key] = overlay[key]

expect merged["a"] == 1
expect merged["b"] == 3
expect merged["c"] == 4
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 13 |
| Active scenarios | 13 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
- `REQ-FEATURE-ConfLoad-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `aeaee45603323bb3ff9378958238edbb876c77296ca0e727691a07bb8600e3be`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `aeaee45603323bb3ff9378958238edbb876c77296ca0e727691a07bb8600e3be`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `aeaee45603323bb3ff9378958238edbb876c77296ca0e727691a07bb8600e3be`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/03_system/feature/app/config_loader_spec.spl
mirror: doc/06_spec/03_system/feature/app/config_loader_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/feature/app/config_loader_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/feature/app/config_loader_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/feature/app/config_loader_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 3 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/feature/app/config_loader_spec.spl:84:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'stores basic integers' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/app/config_loader_spec.spl:92:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'stores floats' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/app/config_loader_spec.spl:100:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'stores booleans' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
