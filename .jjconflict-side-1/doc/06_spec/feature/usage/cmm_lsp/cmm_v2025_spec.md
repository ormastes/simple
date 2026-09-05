# CMM v2025 Version Support

> Tests for CMM v2025 version support and command database updates.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 16 | 16 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# CMM v2025 Version Support

Tests for CMM v2025 version support and command database updates.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Tooling |
| Status | In Progress |
| Source | `test/feature/usage/cmm_lsp/cmm_v2025_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests for CMM v2025 version support and command database updates.

## Scenarios

### CmmVersion V2025

#### config_for_version recognizes 2025

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- config_for_version recognizes 2025
- config_for_version recognizes 2025
   - Expected: version_name(cfg.version) equals `2025`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("config_for_version recognizes 2025")
step("config_for_version recognizes 2025")
# @req: REQ-FEAT-CMM-LSP-CMM-V2025-SPEC-001
val cfg = config_for_version("2025")
expect(version_name(cfg.version)).to_equal("2025")
```

</details>

#### V2025 has all features

- V2025 has all features
- V2025 has all features
   - Expected: has_feature(cfg, "GLOBALON") is true
   - Expected: has_feature(cfg, "PRIVATE") is true
   - Expected: has_feature(cfg, "WRITEB") is true
   - Expected: has_feature(cfg, "LUA") is true
   - Expected: has_feature(cfg, "OBJAPI") is true
   - Expected: has_feature(cfg, "I2C") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("V2025 has all features")
step("V2025 has all features")
val cfg = config_for_version("2025")
expect(has_feature(cfg, "GLOBALON")).to_equal(true)
expect(has_feature(cfg, "PRIVATE")).to_equal(true)
expect(has_feature(cfg, "WRITEB")).to_equal(true)
expect(has_feature(cfg, "LUA")).to_equal(true)
expect(has_feature(cfg, "OBJAPI")).to_equal(true)
expect(has_feature(cfg, "I2C")).to_equal(true)
```

</details>

#### V2013 does not have V2025 features

- V2013 does not have V2025 features
- V2013 does not have V2025 features
   - Expected: has_feature(cfg, "LUA") is false
   - Expected: has_feature(cfg, "OBJAPI") is false
   - Expected: has_feature(cfg, "I2C") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("V2013 does not have V2025 features")
step("V2013 does not have V2025 features")
val cfg = config_for_version("2013")
expect(has_feature(cfg, "LUA")).to_equal(false)
expect(has_feature(cfg, "OBJAPI")).to_equal(false)
expect(has_feature(cfg, "I2C")).to_equal(false)
```

</details>

#### V2012 does not have V2025 or V2013 features

- V2012 does not have V2025 or V2013 features
- V2012 does not have V2025 or V2013 features
   - Expected: has_feature(cfg, "GLOBALON") is false
   - Expected: has_feature(cfg, "LUA") is false
   - Expected: has_feature(cfg, "I2C") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("V2012 does not have V2025 or V2013 features")
step("V2012 does not have V2025 or V2013 features")
val cfg = config_for_version("2012")
expect(has_feature(cfg, "GLOBALON")).to_equal(false)
expect(has_feature(cfg, "LUA")).to_equal(false)
expect(has_feature(cfg, "I2C")).to_equal(false)
```

</details>

#### Latest has all features

- Latest has all features
- Latest has all features
   - Expected: has_feature(cfg, "LUA") is true
   - Expected: has_feature(cfg, "OBJAPI") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("Latest has all features")
step("Latest has all features")
val cfg = default_config()
expect(has_feature(cfg, "LUA")).to_equal(true)
expect(has_feature(cfg, "OBJAPI")).to_equal(true)
```

</details>

### CMM v2025 commands in DB

#### Lua commands are in database

- Lua commands are in database
- Lua commands are in database
   - Expected: cmd == nil is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("Lua commands are in database")
step("Lua commands are in database")
val db = build_command_db()
val cmd = lookup_command(db, "LUA.RUN")
expect(cmd == nil).to_equal(false)
```

</details>

#### I2C commands are in database

- I2C commands are in database
- I2C commands are in database
   - Expected: cmd == nil is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("I2C commands are in database")
step("I2C commands are in database")
val db = build_command_db()
val cmd = lookup_command(db, "I2C.Read")
expect(cmd == nil).to_equal(false)
```

</details>

#### Object API commands are in database

- Object API commands are in database
- Object API commands are in database
   - Expected: cmd == nil is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("Object API commands are in database")
step("Object API commands are in database")
val db = build_command_db()
val cmd = lookup_command(db, "Obj.Buffer.Create")
expect(cmd == nil).to_equal(false)
```

</details>

#### API lock commands are in database

- API lock commands are in database
- API lock commands are in database
   - Expected: cmd == nil is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("API lock commands are in database")
step("API lock commands are in database")
val db = build_command_db()
val cmd = lookup_command(db, "API.LOCK")
expect(cmd == nil).to_equal(false)
```

</details>

#### Lua commands have min_version 2025

- Lua commands have min_version 2025
- Lua commands have min_version 2025
   - Expected: c.min_version equals `2025`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("Lua commands have min_version 2025")
step("Lua commands have min_version 2025")
val db = build_command_db()
val cmd = lookup_command(db, "LUA.RUN")
if cmd.?:
    val c = cmd.unwrap()
    expect(c.min_version).to_equal("2025")
```

</details>

#### Lua group has multiple commands

- Lua group has multiple commands
- Lua group has multiple commands


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("Lua group has multiple commands")
step("Lua group has multiple commands")
val db = build_command_db()
val lua_cmds = get_group_commands(db, "Lua")
expect(lua_cmds.len()).to_be_greater_than(3)
```

</details>

#### ObjectAPI group has multiple commands

- ObjectAPI group has multiple commands
- ObjectAPI group has multiple commands


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("ObjectAPI group has multiple commands")
step("ObjectAPI group has multiple commands")
val db = build_command_db()
val obj_cmds = get_group_commands(db, "ObjectAPI")
expect(obj_cmds.len()).to_be_greater_than(5)
```

</details>

#### completion suggests Lua commands

- completion suggests Lua commands
- completion suggests Lua commands


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("completion suggests Lua commands")
step("completion suggests Lua commands")
val db = build_command_db()
val matches = get_completions(db, "LUA.")
expect(matches.len()).to_be_greater_than(0)
```

</details>

### CMM v2025 parsing

#### parses Lua commands without errors

- parses Lua commands without errors
- parses Lua commands without errors
   - Expected: program.errors.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses Lua commands without errors")
step("parses Lua commands without errors")
val source = "LUA.RUN \"test.lua\"\nENDDO"
val program = parse_cmm_source(source, "<test>")
expect(program.errors.len()).to_equal(0)
```

</details>

#### parses Object API commands

- parses Object API commands
- parses Object API commands
   - Expected: program.errors.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses Object API commands")
step("parses Object API commands")
val source = "Obj.Buffer.Create mybuf 1024.\nENDDO"
val program = parse_cmm_source(source, "<test>")
expect(program.errors.len()).to_equal(0)
```

</details>

#### parses I2C commands

- parses I2C commands
- parses I2C commands
   - Expected: program.errors.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses I2C commands")
step("parses I2C commands")
val source = "I2C.Read 0x50 0x00 8.\nENDDO"
val program = parse_cmm_source(source, "<test>")
expect(program.errors.len()).to_equal(0)
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-FEATURE`
- `REQ-FEAT-CMM-LSP-CMM-V2025-SPEC-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `9a5edff0ad71a99f1843d79ce095978452b626bc1f90fa92cdb024b03d2d3a80`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `9a5edff0ad71a99f1843d79ce095978452b626bc1f90fa92cdb024b03d2d3a80`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `9a5edff0ad71a99f1843d79ce095978452b626bc1f90fa92cdb024b03d2d3a80`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/feature/usage/cmm_lsp/cmm_v2025_spec.spl
mirror: doc/06_spec/feature/usage/cmm_lsp/cmm_v2025_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/feature/usage/cmm_lsp/cmm_v2025_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/feature/usage/cmm_lsp/cmm_v2025_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/feature/usage/cmm_lsp/cmm_v2025_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 3 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/feature/usage/cmm_lsp/cmm_v2025_spec.spl:39:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'config_for_version recognizes 2025' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/usage/cmm_lsp/cmm_v2025_spec.spl:47:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'V2025 has all features' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/usage/cmm_lsp/cmm_v2025_spec.spl:59:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'V2013 does not have V2025 features' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
