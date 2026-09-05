# CMM v2025 Version Support

> Tests for CMM v2025 version support and command database updates.

<!-- sdn-diagram:id=cmm_v2025_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=cmm_v2025_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

cmm_v2025_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=cmm_v2025_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

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
| Source | `test/03_system/feature/usage/cmm_lsp/cmm_v2025_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests for CMM v2025 version support and command database updates.

## Scenarios

### CmmVersion V2025

#### config_for_version recognizes 2025

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cfg = config_for_version("2025")
expect(version_name(cfg.version)).to_equal("2025")
```

</details>

#### V2025 has all features

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cfg = config_for_version("2013")
expect(has_feature(cfg, "LUA")).to_equal(false)
expect(has_feature(cfg, "OBJAPI")).to_equal(false)
expect(has_feature(cfg, "I2C")).to_equal(false)
```

</details>

#### V2012 does not have V2025 or V2013 features

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cfg = config_for_version("2012")
expect(has_feature(cfg, "GLOBALON")).to_equal(false)
expect(has_feature(cfg, "LUA")).to_equal(false)
expect(has_feature(cfg, "I2C")).to_equal(false)
```

</details>

#### Latest has all features

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cfg = default_config()
expect(has_feature(cfg, "LUA")).to_equal(true)
expect(has_feature(cfg, "OBJAPI")).to_equal(true)
```

</details>

### CMM v2025 commands in DB

#### Lua commands are in database

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val db = build_command_db()
val cmd = lookup_command(db, "LUA.RUN")
expect(cmd.?).to_equal(true)
```

</details>

#### I2C commands are in database

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val db = build_command_db()
val cmd = lookup_command(db, "I2C.Read")
expect(cmd.?).to_equal(true)
```

</details>

#### Object API commands are in database

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val db = build_command_db()
val cmd = lookup_command(db, "Obj.Buffer.Create")
expect(cmd.?).to_equal(true)
```

</details>

#### API lock commands are in database

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val db = build_command_db()
val cmd = lookup_command(db, "API.LOCK")
expect(cmd.?).to_equal(true)
```

</details>

#### Lua commands have min_version 2025

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val db = build_command_db()
val cmd = lookup_command(db, "LUA.RUN")
if cmd.?:
    val c = cmd.unwrap()
    expect(c.min_version).to_equal("2025")
```

</details>

#### Lua group has multiple commands

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val db = build_command_db()
val lua_cmds = get_group_commands(db, "Lua")
expect(lua_cmds.len()).to_be_greater_than(3)
```

</details>

#### ObjectAPI group has multiple commands

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val db = build_command_db()
val obj_cmds = get_group_commands(db, "ObjectAPI")
expect(obj_cmds.len()).to_be_greater_than(5)
```

</details>

#### completion suggests Lua commands

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val db = build_command_db()
val matches = get_completions(db, "LUA.")
expect(matches.len()).to_be_greater_than(0)
```

</details>

### CMM v2025 parsing

#### parses Lua commands without errors

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "LUA.RUN \"test.lua\"\nENDDO"
val program = parse_cmm_source(source, "<test>")
expect(program.errors.len()).to_equal(0)
```

</details>

#### parses Object API commands

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "Obj.Buffer.Create mybuf 1024.\nENDDO"
val program = parse_cmm_source(source, "<test>")
expect(program.errors.len()).to_equal(0)
```

</details>

#### parses I2C commands

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
