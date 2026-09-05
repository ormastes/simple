# T32 Gdb Bridge Specification

> Tests covering T32GdbBridgeConfig creation, T32 PRACTICE command formatting.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# T32 Gdb Bridge Specification

## Scenarios

### T32GdbBridgeConfig creation

#### T32 target config has correct T32 port

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- T32 target config has correct T32 port
   - Expected: cfg.t32_port equals `20000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("T32 target config has correct T32 port")
val cfg = T32GdbBridgeConfig.for_t32_target()
expect(cfg.t32_port).to_equal(20000)
```

</details>

#### T32 target config has correct GDB port

- T32 target config has correct GDB port
   - Expected: cfg.gdb_port equals `2331`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("T32 target config has correct GDB port")
val cfg = T32GdbBridgeConfig.for_t32_target()
expect(cfg.gdb_port).to_equal(2331)
```

</details>

#### T32 target config has correct name

- T32 target config has correct name
   - Expected: cfg.target_name equals `T32 Power Debug`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("T32 target config has correct name")
val cfg = T32GdbBridgeConfig.for_t32_target()
expect(cfg.target_name).to_equal("T32 Power Debug")
```

</details>

### T32 PRACTICE command formatting

#### GDB server enable command

- GDB server enable command
   - Expected: cfg.gdb_server_enable_cmd() equals `System.Option GDBSERVER ON`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("GDB server enable command")
val cfg = T32GdbBridgeConfig.for_t32_target()
expect(cfg.gdb_server_enable_cmd()).to_equal("System.Option GDBSERVER ON")
```

</details>

#### GDB server port command

- GDB server port command
   - Expected: cfg.gdb_server_port_cmd() equals `GDBSERVER.PORT 2331`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("GDB server port command")
val cfg = T32GdbBridgeConfig.for_t32_target()
expect(cfg.gdb_server_port_cmd()).to_equal("GDBSERVER.PORT 2331")
```

</details>

#### GDB server disable command

- GDB server disable command
   - Expected: cfg.gdb_server_disable_cmd() equals `System.Option GDBSERVER OFF`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("GDB server disable command")
val cfg = T32GdbBridgeConfig.for_t32_target()
expect(cfg.gdb_server_disable_cmd()).to_equal("System.Option GDBSERVER OFF")
```

</details>

#### PRACTICE DO command

- PRACTICE DO command
   - Expected: cmd equals `DO t32_startup.cmm`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("PRACTICE DO command")
val cmd = format_practice_do("t32_startup.cmm")
expect(cmd).to_equal("DO t32_startup.cmm")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/unit/app/debug/remote/t32_gdb_bridge_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering T32GdbBridgeConfig creation, T32 PRACTICE command formatting.
- T32GdbBridgeConfig creation
- T32 PRACTICE command formatting

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `46522ae624cb6195d80b5ba2eefb688bb434887354d2e1ee2df5f438f6fe769d`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `46522ae624cb6195d80b5ba2eefb688bb434887354d2e1ee2df5f438f6fe769d`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `46522ae624cb6195d80b5ba2eefb688bb434887354d2e1ee2df5f438f6fe769d`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/unit/app/debug/remote/t32_gdb_bridge_spec.spl
mirror: doc/06_spec/unit/app/debug/remote/t32_gdb_bridge_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/app/debug/remote/t32_gdb_bridge_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/app/debug/remote/t32_gdb_bridge_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/app/debug/remote/t32_gdb_bridge_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/app/debug/remote/t32_gdb_bridge_spec.spl:44:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'T32 target config has correct T32 port' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/debug/remote/t32_gdb_bridge_spec.spl:50:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'T32 target config has correct GDB port' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/debug/remote/t32_gdb_bridge_spec.spl:56:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'T32 target config has correct name' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
