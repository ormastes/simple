# fileio_protection_spec

> Purpose: this manual pins the behavior named "File I/O Protection Engine" for the owning engineering team.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 27 | 27 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# fileio_protection_spec

Purpose: this manual pins the behavior named "File I/O Protection Engine" for the owning engineering team.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/unit/app/mcp_unit/fileio_protection_spec.spl` |
| Updated | 2026-08-27 |
| Generator | `simple spipe-docgen` (Simple) |

Purpose: this manual pins the behavior named "File I/O Protection Engine" for the owning engineering team.
    Audience: engineers verifying regressions in this area; steps below are executable evidence.

## Scenarios

### File I/O Protection Engine

### Rule Matching

#### matches exact paths

- matches exact paths


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("matches exact paths")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
val engine = ProtectionEngine(rules: [], temp_base: "/tmp")
engine.add_rule("CLAUDE.md", RuleType.Exact, RuleAction.Protect, "Test")

val result = engine.check_path("CLAUDE.md", "write")
match result:
    ProtectionResult.Denied(_): assert true
    _: fail("Expected denied result")
```

</details>

#### matches glob patterns with *

- matches glob patterns with *


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("matches glob patterns with *")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
val engine = ProtectionEngine(rules: [], temp_base: "/tmp")
engine.add_rule("*.sdn", RuleType.Glob, RuleAction.Atomic, "Test")

val result = engine.check_path("test.sdn", "write")
match result:
    ProtectionResult.RequiresAtomic: assert true
    _: fail("Expected requires atomic")
```

</details>

#### matches glob patterns with multiple *

- matches glob patterns with multiple *


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("matches glob patterns with multiple *")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
val engine = ProtectionEngine(rules: [], temp_base: "/tmp")
engine.add_rule("doc/*.sdn", RuleType.Glob, RuleAction.Atomic, "Test")

val result = engine.check_path("doc/test.sdn", "write")
match result:
    ProtectionResult.RequiresAtomic: assert true
    _: fail("Expected requires atomic")
```

</details>

#### does not match non-matching patterns

- does not match non-matching patterns


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("does not match non-matching patterns")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
val engine = ProtectionEngine(rules: [], temp_base: "/tmp")
engine.add_rule("*.sdn", RuleType.Glob, RuleAction.Atomic, "Test")

val result = engine.check_path("test.txt", "write")
match result:
    ProtectionResult.Allowed: assert true
    _: fail("Expected allowed")
```

</details>

#### normalizes paths with trailing slash

- normalizes paths with trailing slash


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("normalizes paths with trailing slash")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
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

- normalizes relative paths


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("normalizes relative paths")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
val engine = ProtectionEngine(rules: [], temp_base: "/tmp")
engine.add_rule("test.txt", RuleType.Exact, RuleAction.Protect, "Test")

val result = engine.check_path("./test.txt", "write")
match result:
    ProtectionResult.Denied(_): assert true
    _: fail("Expected denied")
```

</details>

#### returns first matching rule

- returns first matching rule


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("returns first matching rule")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
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

- allows read on protected files


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("allows read on protected files")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
val engine = ProtectionEngine(rules: [], temp_base: "/tmp")
engine.add_rule("test.txt", RuleType.Exact, RuleAction.Protect, "Test")

val result = engine.check_path("test.txt", "read")
match result:
    ProtectionResult.Allowed: assert true
    _: fail("Expected allowed for read")
```

</details>

#### denies write on protected files

- denies write on protected files


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("denies write on protected files")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
val engine = ProtectionEngine(rules: [], temp_base: "/tmp")
engine.add_rule("test.txt", RuleType.Exact, RuleAction.Protect, "Test")

val result = engine.check_path("test.txt", "write")
match result:
    ProtectionResult.Denied(_): assert true
    _: fail("Expected denied for write")
```

</details>

#### denies delete on protected files

- denies delete on protected files


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("denies delete on protected files")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
val engine = ProtectionEngine(rules: [], temp_base: "/tmp")
engine.add_rule("test.txt", RuleType.Exact, RuleAction.Protect, "Test")

val result = engine.check_path("test.txt", "delete")
match result:
    ProtectionResult.Denied(_): assert true
    _: fail("Expected denied for delete")
```

</details>

#### denies all operations on denied files

- denies all operations on denied files


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("denies all operations on denied files")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
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

- redirects files to temp directory


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("redirects files to temp directory")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
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

- requires atomic writes for atomic action


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("requires atomic writes for atomic action")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
val engine = ProtectionEngine(rules: [], temp_base: "/tmp")
engine.add_rule("*.sdn", RuleType.Glob, RuleAction.Atomic, "Test")

val result = engine.check_path("test.sdn", "write")
match result:
    ProtectionResult.RequiresAtomic: assert true
    _: fail("Expected requires atomic")
```

</details>

#### allows all operations for allow action

- allows all operations for allow action


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("allows all operations for allow action")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
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

- handles empty path


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("handles empty path")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
val engine = ProtectionEngine(rules: [], temp_base: "/tmp")
val result = engine.check_path("", "write")
match result:
    ProtectionResult.Allowed: assert true
    _: fail("Expected allowed for empty path")
```

</details>

#### handles no matching rules

- handles no matching rules


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("handles no matching rules")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
val engine = ProtectionEngine(rules: [], temp_base: "/tmp")
val result = engine.check_path("random.txt", "write")
match result:
    ProtectionResult.Allowed: assert true
    _: fail("Expected allowed when no rules match")
```

</details>

#### handles nested paths

- handles nested paths


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("handles nested paths")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
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

- handles multiple rules for same path


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("handles multiple rules for same path")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
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

- lists protected files with wildcard
   - Expected: files.len() equals `2`
   - Expected: files contains `CLAUDE.md`
   - Expected: files contains `src/`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("lists protected files with wildcard")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
val engine = ProtectionEngine(rules: [], temp_base: "/tmp")
engine.add_rule("CLAUDE.md", RuleType.Exact, RuleAction.Protect, "Test 1")
engine.add_rule("src/", RuleType.Exact, RuleAction.Protect, "Test 2")
engine.add_rule("*.txt", RuleType.Glob, RuleAction.Allow, "Test 3")

val files = engine.list_protected_files("*")
expect(files.len()).to_equal(2)  # oracle: files.len() must equal 2 — authoritative contract constant
expect(files.contains("CLAUDE.md")).to_equal(true)
expect(files.contains("src/")).to_equal(true)
```

</details>

#### lists protected files with pattern

- lists protected files with pattern
   - Expected: files.len() equals `1`
   - Expected: files contains `CLAUDE.md`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("lists protected files with pattern")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
val engine = ProtectionEngine(rules: [], temp_base: "/tmp")
engine.add_rule("CLAUDE.md", RuleType.Exact, RuleAction.Protect, "Test 1")
engine.add_rule("src/", RuleType.Exact, RuleAction.Protect, "Test 2")

val files = engine.list_protected_files("CLAUDE")
expect(files.len()).to_equal(1)  # oracle: files.len() must equal 1 — authoritative contract constant
expect(files.contains("CLAUDE.md")).to_equal(true)
```

</details>

#### gets protection info for path

- gets protection info for path
   - Expected: info contains `Protect`
   - Expected: info contains `Important file`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("gets protection info for path")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
val engine = ProtectionEngine(rules: [], temp_base: "/tmp")
engine.add_rule("CLAUDE.md", RuleType.Exact, RuleAction.Protect, "Important file")

val info = engine.get_protection_info("CLAUDE.md")
expect(info.contains("Protect")).to_equal(true)
expect(info.contains("Important file")).to_equal(true)
```

</details>

#### gets protection info for unprotected path

- gets protection info for unprotected path
   - Expected: info contains `No protection`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("gets protection info for unprotected path")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
val engine = ProtectionEngine(rules: [], temp_base: "/tmp")
val info = engine.get_protection_info("random.txt")
expect(info.contains("No protection")).to_equal(true)
```

</details>

### Server Integration

#### safe_atomic_write uses protection checks

- safe_atomic_write uses protection checks


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("safe_atomic_write uses protection checks")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
val source = read_file("src/lib/nogc_async_mut/mcp/fileio_server.spl")
expect(source).to_contain("fn tool_safe_atomic_write")
expect(source).to_contain("check_path(path, \"write\")")
expect(source).to_contain("Atomic write denied")
```

</details>

#### default engine denies new root entries

- default engine denies new root entries


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("default engine denies new root entries")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
val engine = create_engine("missing_workspace_root_guard_config.sdn", "/tmp")
val result = engine.check_path("new_root_file.tmp", "write")
match result:
    ProtectionResult.Denied(reason):
        check(reason.contains("Workspace root policy"))
    _: fail("Expected workspace root policy denial")
```

</details>

#### default engine denies new immediate child entries

- default engine denies new immediate child entries


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("default engine denies new immediate child entries")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
val engine = create_engine("missing_workspace_root_guard_config.sdn", "/tmp")
val result = engine.check_path("src/new_child_entry", "write")
match result:
    ProtectionResult.Denied(reason):
        check(reason.contains("Workspace root policy"))
    _: fail("Expected workspace root child policy denial")
```

</details>

#### default engine keeps mutable build directory writable

- default engine keeps mutable build directory writable


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("default engine keeps mutable build directory writable")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
val engine = create_engine("missing_workspace_root_guard_config.sdn", "/tmp")
val result = engine.check_path("build/new_artifact.tmp", "write")
match result:
    ProtectionResult.Allowed: assert true
    _: fail("Expected build artifact path to remain writable")
```

</details>

#### configured engine still installs workspace root policy

- configured engine still installs workspace root policy


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("configured engine still installs workspace root policy")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
val engine = create_engine("config/critical_files.sdn", "/tmp")
val result = engine.check_path("another_root_file.tmp", "write")
match result:
    ProtectionResult.Denied(reason):
        check(reason.contains("Workspace root policy"))
    _: fail("Expected configured engine to retain root policy")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 27 |
| Active scenarios | 27 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-APP`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `5f5e3bf23fb5211f3db1d54ce37f3b846c29b060d5f4689287a4831a41f67840`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `5f5e3bf23fb5211f3db1d54ce37f3b846c29b060d5f4689287a4831a41f67840`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `5f5e3bf23fb5211f3db1d54ce37f3b846c29b060d5f4689287a4831a41f67840`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **97/100**; effective score: **97/100**; blockers: **0**.

SSpec documentization score: 97/100
source: test/unit/app/mcp_unit/fileio_protection_spec.spl
mirror: doc/06_spec/unit/app/mcp_unit/fileio_protection_spec.md (current)
findings: 2 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=100 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/app/mcp_unit/fileio_protection_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/app/mcp_unit/fileio_protection_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
<!-- sspec-maintain:scorecard:end -->
