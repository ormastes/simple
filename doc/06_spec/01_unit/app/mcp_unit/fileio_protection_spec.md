# Fileio Protection Specification

> 1. engine add rule

<!-- sdn-diagram:id=fileio_protection_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=fileio_protection_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

fileio_protection_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=fileio_protection_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 27 | 27 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Fileio Protection Specification

## Scenarios

### File I/O Protection Engine

### Rule Matching

#### matches exact paths

1. engine add rule
2. ProtectionResult Denied
3.  : fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val engine = ProtectionEngine(rules: [], temp_base: "/tmp")
engine.add_rule("CLAUDE.md", RuleType.Exact, RuleAction.Protect, "Test")

val result = engine.check_path("CLAUDE.md", "write")
match result:
    ProtectionResult.Denied(_): assert true
    _: fail("Expected denied result")
```

</details>

#### matches glob patterns with *

1. engine add rule
2.  : fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val engine = ProtectionEngine(rules: [], temp_base: "/tmp")
engine.add_rule("*.sdn", RuleType.Glob, RuleAction.Atomic, "Test")

val result = engine.check_path("test.sdn", "write")
match result:
    ProtectionResult.RequiresAtomic: assert true
    _: fail("Expected requires atomic")
```

</details>

#### matches glob patterns with multiple *

1. engine add rule
2.  : fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val engine = ProtectionEngine(rules: [], temp_base: "/tmp")
engine.add_rule("doc/*.sdn", RuleType.Glob, RuleAction.Atomic, "Test")

val result = engine.check_path("doc/test.sdn", "write")
match result:
    ProtectionResult.RequiresAtomic: assert true
    _: fail("Expected requires atomic")
```

</details>

#### does not match non-matching patterns

1. engine add rule
2.  : fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val engine = ProtectionEngine(rules: [], temp_base: "/tmp")
engine.add_rule("*.sdn", RuleType.Glob, RuleAction.Atomic, "Test")

val result = engine.check_path("test.txt", "write")
match result:
    ProtectionResult.Allowed: assert true
    _: fail("Expected allowed")
```

</details>

#### normalizes paths with trailing slash

1. engine add rule
2. ProtectionResult Denied
3.  : fail
4. ProtectionResult Denied
5.  : fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val engine = ProtectionEngine(rules: [], temp_base: "/tmp")
engine.add_rule("src/", RuleType.Exact, RuleAction.Protect, "Test")

val result1 = engine.check_path("src/", "write")
val result2 = engine.check_path("src", "write")

match result1:
    ProtectionResult.Denied(_): assert true
    _: fail("Expected denied for src/")

match result2:
    ProtectionResult.Denied(_): assert true
    _: fail("Expected denied for src")
```

</details>

#### normalizes relative paths

1. engine add rule
2. ProtectionResult Denied
3.  : fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val engine = ProtectionEngine(rules: [], temp_base: "/tmp")
engine.add_rule("test.txt", RuleType.Exact, RuleAction.Protect, "Test")

val result = engine.check_path("./test.txt", "write")
match result:
    ProtectionResult.Denied(_): assert true
    _: fail("Expected denied")
```

</details>

#### returns first matching rule

1. engine add rule
2. engine add rule
3. ProtectionResult Denied
4. check
5.  : fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val engine = ProtectionEngine(rules: [], temp_base: "/tmp")
engine.add_rule("*.txt", RuleType.Glob, RuleAction.Deny, "First")
engine.add_rule("*.txt", RuleType.Glob, RuleAction.Allow, "Second")

val result = engine.check_path("test.txt", "write")
match result:
    ProtectionResult.Denied(reason):
        check(reason.contains("First"))
    _: fail("Expected first rule to match")
```

</details>

### Action Enforcement

#### allows read on protected files

1. engine add rule
2.  : fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val engine = ProtectionEngine(rules: [], temp_base: "/tmp")
engine.add_rule("test.txt", RuleType.Exact, RuleAction.Protect, "Test")

val result = engine.check_path("test.txt", "read")
match result:
    ProtectionResult.Allowed: assert true
    _: fail("Expected allowed for read")
```

</details>

#### denies write on protected files

1. engine add rule
2. ProtectionResult Denied
3.  : fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val engine = ProtectionEngine(rules: [], temp_base: "/tmp")
engine.add_rule("test.txt", RuleType.Exact, RuleAction.Protect, "Test")

val result = engine.check_path("test.txt", "write")
match result:
    ProtectionResult.Denied(_): assert true
    _: fail("Expected denied for write")
```

</details>

#### denies delete on protected files

1. engine add rule
2. ProtectionResult Denied
3.  : fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val engine = ProtectionEngine(rules: [], temp_base: "/tmp")
engine.add_rule("test.txt", RuleType.Exact, RuleAction.Protect, "Test")

val result = engine.check_path("test.txt", "delete")
match result:
    ProtectionResult.Denied(_): assert true
    _: fail("Expected denied for delete")
```

</details>

#### denies all operations on denied files

1. engine add rule
2. ProtectionResult Denied
3.  : fail
4. ProtectionResult Denied
5.  : fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val engine = ProtectionEngine(rules: [], temp_base: "/tmp")
engine.add_rule("/", RuleType.Exact, RuleAction.Deny, "Test")

val read_result = engine.check_path("/", "read")
val write_result = engine.check_path("/", "write")

match read_result:
    ProtectionResult.Denied(_): assert true
    _: fail("Expected denied for read")

match write_result:
    ProtectionResult.Denied(_): assert true
    _: fail("Expected denied for write")
```

</details>

#### redirects files to temp directory

1. engine add rule
2. ProtectionResult Redirected
3. check
4. check
5.  : fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val engine = ProtectionEngine(rules: [], temp_base: "/tmp/test")
engine.add_rule("*.sh", RuleType.Glob, RuleAction.Redirect, "Test")

val result = engine.check_path("script.sh", "write")
match result:
    ProtectionResult.Redirected(path):
        check(path.contains("/tmp/test"))
        check(path.contains("script.sh"))
    _: fail("Expected redirected")
```

</details>

#### requires atomic writes for atomic action

1. engine add rule
2.  : fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val engine = ProtectionEngine(rules: [], temp_base: "/tmp")
engine.add_rule("*.sdn", RuleType.Glob, RuleAction.Atomic, "Test")

val result = engine.check_path("test.sdn", "write")
match result:
    ProtectionResult.RequiresAtomic: assert true
    _: fail("Expected requires atomic")
```

</details>

#### allows all operations for allow action

1. engine add rule
2.  : fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val engine = ProtectionEngine(rules: [], temp_base: "/tmp")
engine.add_rule("doc/", RuleType.Exact, RuleAction.Allow, "Test")

val result = engine.check_path("doc/", "write")
match result:
    ProtectionResult.Allowed: assert true
    _: fail("Expected allowed")
```

</details>

### Edge Cases

#### handles empty path

1.  : fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val engine = ProtectionEngine(rules: [], temp_base: "/tmp")
val result = engine.check_path("", "write")
match result:
    ProtectionResult.Allowed: assert true
    _: fail("Expected allowed for empty path")
```

</details>

#### handles no matching rules

1.  : fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val engine = ProtectionEngine(rules: [], temp_base: "/tmp")
val result = engine.check_path("random.txt", "write")
match result:
    ProtectionResult.Allowed: assert true
    _: fail("Expected allowed when no rules match")
```

</details>

#### handles nested paths

1. engine add rule
2.  : fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val engine = ProtectionEngine(rules: [], temp_base: "/tmp")
engine.add_rule("src/", RuleType.Exact, RuleAction.Protect, "Test")

# Should not match nested paths
val result = engine.check_path("src/app/main.spl", "write")
match result:
    ProtectionResult.Allowed: assert true
    _: fail("Expected allowed for nested path")
```

</details>

#### handles multiple rules for same path

1. engine add rule
2. engine add rule
3. ProtectionResult Denied
4. check
5.  : fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val engine = ProtectionEngine(rules: [], temp_base: "/tmp")
engine.add_rule("test.txt", RuleType.Exact, RuleAction.Protect, "Rule 1")
engine.add_rule("test.txt", RuleType.Exact, RuleAction.Allow, "Rule 2")

# First rule should win
val result = engine.check_path("test.txt", "write")
match result:
    ProtectionResult.Denied(reason):
        check(reason.contains("Rule 1"))
    _: fail("Expected first rule to match")
```

</details>

#### lists protected files with wildcard

1. engine add rule
2. engine add rule
3. engine add rule
   - Expected: files.len() equals `2`
   - Expected: files contains `CLAUDE.md`
   - Expected: files contains `src/`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val engine = ProtectionEngine(rules: [], temp_base: "/tmp")
engine.add_rule("CLAUDE.md", RuleType.Exact, RuleAction.Protect, "Test 1")
engine.add_rule("src/", RuleType.Exact, RuleAction.Protect, "Test 2")
engine.add_rule("*.txt", RuleType.Glob, RuleAction.Allow, "Test 3")

val files = engine.list_protected_files("*")
expect(files.len()).to_equal(2)
expect(files.contains("CLAUDE.md")).to_equal(true)
expect(files.contains("src/")).to_equal(true)
```

</details>

#### lists protected files with pattern

1. engine add rule
2. engine add rule
   - Expected: files.len() equals `1`
   - Expected: files contains `CLAUDE.md`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val engine = ProtectionEngine(rules: [], temp_base: "/tmp")
engine.add_rule("CLAUDE.md", RuleType.Exact, RuleAction.Protect, "Test 1")
engine.add_rule("src/", RuleType.Exact, RuleAction.Protect, "Test 2")

val files = engine.list_protected_files("CLAUDE")
expect(files.len()).to_equal(1)
expect(files.contains("CLAUDE.md")).to_equal(true)
```

</details>

#### gets protection info for path

1. engine add rule
   - Expected: info contains `Protect`
   - Expected: info contains `Important file`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val engine = ProtectionEngine(rules: [], temp_base: "/tmp")
engine.add_rule("CLAUDE.md", RuleType.Exact, RuleAction.Protect, "Important file")

val info = engine.get_protection_info("CLAUDE.md")
expect(info.contains("Protect")).to_equal(true)
expect(info.contains("Important file")).to_equal(true)
```

</details>

#### gets protection info for unprotected path

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val engine = ProtectionEngine(rules: [], temp_base: "/tmp")
val info = engine.get_protection_info("random.txt")
expect(info.contains("No protection")).to_equal(true)
```

</details>

### Server Integration

#### safe_atomic_write uses protection checks

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = read_file("src/lib/nogc_async_mut/mcp/fileio_server.spl")
expect(source.contains("fn tool_safe_atomic_write")).to_equal(true)
expect(source.contains("check_path(path, \"write\")")).to_equal(true)
expect(source.contains("Atomic write denied")).to_equal(true)
```

</details>

#### default engine denies new root entries

1. ProtectionResult Denied
2. check
3.  : fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val engine = create_engine("missing_workspace_root_guard_config.sdn", "/tmp")
val result = engine.check_path("new_root_file.tmp", "write")
match result:
    ProtectionResult.Denied(reason):
        check(reason.contains("Workspace root policy"))
    _: fail("Expected workspace root policy denial")
```

</details>

#### default engine denies new immediate child entries

1. ProtectionResult Denied
2. check
3.  : fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val engine = create_engine("missing_workspace_root_guard_config.sdn", "/tmp")
val result = engine.check_path("src/new_child_entry", "write")
match result:
    ProtectionResult.Denied(reason):
        check(reason.contains("Workspace root policy"))
    _: fail("Expected workspace root child policy denial")
```

</details>

#### default engine keeps mutable build directory writable

1.  : fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val engine = create_engine("missing_workspace_root_guard_config.sdn", "/tmp")
val result = engine.check_path("build/new_artifact.tmp", "write")
match result:
    ProtectionResult.Allowed: assert true
    _: fail("Expected build artifact path to remain writable")
```

</details>

#### configured engine still installs workspace root policy

1. ProtectionResult Denied
2. check
3.  : fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val engine = create_engine("config/critical_files.sdn", "/tmp")
val result = engine.check_path("another_root_file.tmp", "write")
match result:
    ProtectionResult.Denied(reason):
        check(reason.contains("Workspace root policy"))
    _: fail("Expected configured engine to retain root policy")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/mcp_unit/fileio_protection_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- File I/O Protection Engine
- Rule Matching
- Action Enforcement
- Edge Cases
- Server Integration

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 27 |
| Active scenarios | 27 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
