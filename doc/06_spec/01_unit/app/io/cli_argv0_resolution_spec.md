# Cli Argv0 Resolution Specification

> Tests covering CLI argv0 resolution.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Cli Argv0 Resolution Specification

## Scenarios

### CLI argv0 resolution

#### keeps an absolute executable path

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- keeps an absolute executable path
   - Expected: _cli_resolve_argv0("/repo", "/repo/bin/simple") equals `/repo/bin/simple`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps an absolute executable path")
expect(_cli_resolve_argv0("/repo", "/repo/bin/simple")).to_equal("/repo/bin/simple")
```

</details>

#### makes a relative executable path absolute from cwd

- makes a relative executable path absolute from cwd
   - Expected: _cli_resolve_argv0("/repo", "bin/simple") equals `/repo/bin/simple`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("makes a relative executable path absolute from cwd")
expect(_cli_resolve_argv0("/repo", "bin/simple")).to_equal("/repo/bin/simple")
```

</details>

#### rejects a bare command name when no path is known

- rejects a bare command name when no path is known
   - Expected: _cli_resolve_argv0("/repo", "simple") equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects a bare command name when no path is known")
expect(_cli_resolve_argv0("/repo", "simple")).to_equal("")
```

</details>

#### preserves absolute and resolves relative Windows executable paths

- preserves absolute and resolves relative Windows executable paths
   - Expected: _cli_resolve_argv0("C:\\repo", "C:\\repo\\bin\\simple.exe") equals `C:\\repo\\bin\\simple.exe`
   - Expected: _cli_resolve_argv0("C:\\repo", "C:/repo/bin/simple.exe") equals `C:/repo/bin/simple.exe`
   - Expected: _cli_resolve_argv0("C:\\repo", "bin\\simple.exe") equals `C:\\repo/bin\\simple.exe`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("preserves absolute and resolves relative Windows executable paths")
expect(_cli_resolve_argv0("C:\\repo", "C:\\repo\\bin\\simple.exe")).to_equal("C:\\repo\\bin\\simple.exe")
expect(_cli_resolve_argv0("C:\\repo", "C:/repo/bin/simple.exe")).to_equal("C:/repo/bin/simple.exe")
expect(_cli_resolve_argv0("C:\\repo", "bin\\simple.exe")).to_equal("C:\\repo/bin\\simple.exe")
```

</details>

#### preserves UNC executable paths without promoting relative slash paths

- preserves UNC executable paths without promoting relative slash paths
   - Expected: _cli_resolve_argv0("C:\\repo", "\\\\server\\share\\simple.exe") equals `\\\\server\\share\\simple.exe`
   - Expected: _cli_resolve_argv0("/repo", "//server/share/simple") equals `//server/share/simple`
   - Expected: _cli_resolve_argv0("/repo", "tools/simple") equals `/repo/tools/simple`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("preserves UNC executable paths without promoting relative slash paths")
expect(_cli_resolve_argv0("C:\\repo", "\\\\server\\share\\simple.exe")).to_equal("\\\\server\\share\\simple.exe")
expect(_cli_resolve_argv0("/repo", "//server/share/simple")).to_equal("//server/share/simple")
expect(_cli_resolve_argv0("/repo", "tools/simple")).to_equal("/repo/tools/simple")
```

</details>

#### derives the compiled backend sibling for Windows absolute forms

- derives the compiled backend sibling for Windows absolute forms
   - Expected: ui_backend_binary_for_runtime("C:/Simple/simple.exe") equals `C:/Simple/simple_ui_backend.exe`
   - Expected: ui_backend_binary_for_runtime("\\\\server\\share\\simple.exe") equals `\\\\server\\share\\simple_ui_backend.exe`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("derives the compiled backend sibling for Windows absolute forms")
expect(ui_backend_binary_for_runtime("C:/Simple/simple.exe")).to_equal("C:/Simple/simple_ui_backend.exe")
expect(ui_backend_binary_for_runtime("\\\\server\\share\\simple.exe")).to_equal("\\\\server\\share\\simple_ui_backend.exe")
```

</details>

#### resolves our own exe, not the spawned readlink helper

- resolves our own exe, not the spawned readlink helper


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("resolves our own exe, not the spawned readlink helper")
# Regression: `readlink -f /proc/self/exe` resolves the CHILD (readlink
# itself), so exe_path became /usr/bin/readlink -> seed sibling
# /usr/bin/simple_seed missing -> delegate to bin/simple -> fork bomb.
val exe = cli_current_exe_path()
assert_true(exe.len() > 0)
assert_false(exe.ends_with("/readlink"))
assert_false(exe.ends_with("/sh"))
```

</details>

#### establishes its own identity in-process

- establishes its own identity in-process


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("establishes its own identity in-process")
# The shell-out is the defect, not an implementation detail: any
# /proc/self read done by a spawned helper describes the HELPER. Pinned
# positively — a "no readlink" text assertion can't tell code from the
# comments explaining why readlink is wrong.
val source = read_file("src/app/io/cli_ops.spl")
expect(source).to_contain("_cli_resolve_symlink(\"/proc/self/exe\")")
```

</details>

#### canonicalizes a driver override while preserving bare PATH fallback

- canonicalizes a driver override while preserving bare PATH fallback


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("canonicalizes a driver override while preserving bare PATH fallback")
val source = read_file("src/app/io/cli_ops.spl")
expect(source).to_contain("val resolved = _cli_resolve_symlink(path)")
expect(source).to_contain("current == resolved or current == path")
expect(source).to_contain("current.ends_with(\"/\" + path)")
expect(source).to_contain("if _cli_is_current_exe(override):")
expect(source).to_contain("return \"\"")
```

</details>

#### falls back to the repo seed before reporting a missing executable sibling

- falls back to the repo seed before reporting a missing executable sibling


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("falls back to the repo seed before reporting a missing executable sibling")
val source = read_file("src/app/io/cli_ops.spl")
expect(source).to_contain("fn _cli_repo_seed_path() -> text:")
expect(source).to_contain("val candidate = \"bin/simple_seed\"")
expect(source).to_contain("val repo_seed = _cli_repo_seed_path()")
expect(source).to_contain("return repo_seed")
expect(source).to_contain("simple: seed sibling not found")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/io/cli_argv0_resolution_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering CLI argv0 resolution.
- CLI argv0 resolution

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 10 |
| Active scenarios | 10 |
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

- Canonical SPipe generation for source `5ceb3103c0ef52f60795a8513585b814621163231f4614440670d8d8af3ce195`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `5ceb3103c0ef52f60795a8513585b814621163231f4614440670d8d8af3ce195`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `5ceb3103c0ef52f60795a8513585b814621163231f4614440670d8d8af3ce195`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/app/io/cli_argv0_resolution_spec.spl
mirror: doc/06_spec/01_unit/app/io/cli_argv0_resolution_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/app/io/cli_argv0_resolution_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/io/cli_argv0_resolution_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/io/cli_argv0_resolution_spec.spl:16:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps an absolute executable path' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/io/cli_argv0_resolution_spec.spl:21:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'makes a relative executable path absolute from cwd' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/io/cli_argv0_resolution_spec.spl:26:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects a bare command name when no path is known' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
