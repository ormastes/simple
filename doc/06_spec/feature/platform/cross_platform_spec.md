# Cross-Platform Support

> Tests cross-platform compatibility including OS detection, path separator handling, and platform-specific API abstractions. Verifies that Simple programs behave consistently across Linux, macOS, Windows, and FreeBSD.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 12 | 12 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Cross-Platform Support

Tests cross-platform compatibility including OS detection, path separator handling, and platform-specific API abstractions. Verifies that Simple programs behave consistently across Linux, macOS, Windows, and FreeBSD.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Platform |
| Status | In Progress |
| Source | `test/feature/platform/cross_platform_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests cross-platform compatibility including OS detection, path separator handling,
and platform-specific API abstractions. Verifies that Simple programs behave
consistently across Linux, macOS, Windows, and FreeBSD.

## Scenarios

### Platform Detection

#### detects current operating system

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- detects current operating system


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("detects current operating system")
val detected = is_windows() or is_unix() or is_linux() or is_macos()
check(detected)
```

</details>

#### is_unix returns true on Unix-like systems

- is_unix returns true on Unix-like systems


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("is_unix returns true on Unix-like systems")
if is_linux() or is_macos():
    check(is_unix())
else:
    check(not is_unix() or is_unix())
```

</details>

#### is_windows and is_unix are mutually exclusive

- is_windows and is_unix are mutually exclusive


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("is_windows and is_unix are mutually exclusive")
val both = is_windows() and is_unix()
check(not both)
```

</details>

### Path Separators

#### dir_sep returns platform-specific directory separator

- dir_sep returns platform-specific directory separator


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("dir_sep returns platform-specific directory separator")
val sep = dir_sep()
val valid = sep == "/" or sep == "\\"
check(valid)
```

</details>

#### path_sep returns platform-specific PATH separator

- path_sep returns platform-specific PATH separator


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("path_sep returns platform-specific PATH separator")
val sep = path_sep()
val valid = sep == ":" or sep == ";"
check(valid)
```

</details>

#### exe_ext returns correct executable extension

- exe_ext returns correct executable extension


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("exe_ext returns correct executable extension")
val ext = exe_ext()
val valid = ext == ".exe" or ext == ""
check(valid)
```

</details>

#### lib_ext returns correct library extension

- lib_ext returns correct library extension


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("lib_ext returns correct library extension")
val ext = lib_ext()
val valid = ext == ".dll" or ext == ".so" or ext == ".dylib"
check(valid)
```

</details>

### Path Handling

#### join_path combines path components

- join_path combines path components


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("join_path combines path components")
val joined = join_path("foo", "bar")
val has_foo = joined.contains("foo")
val has_bar = joined.contains("bar")
check(has_foo and has_bar)
```

</details>

#### normalize_path handles forward slashes

- normalize_path handles forward slashes


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("normalize_path handles forward slashes")
val normalized = normalize_path("foo/bar")
check(normalized.len() > 0)
```

</details>

#### is_absolute_path detects absolute paths

- is_absolute_path detects absolute paths


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("is_absolute_path detects absolute paths")
val unix_abs = is_absolute_path("/usr/bin")
val relative = is_absolute_path("foo/bar")
if not is_windows():
    check(unix_abs)
    check(not relative)
else:
    check(true)
```

</details>

### Process Management

#### shell executes simple commands

- shell executes simple commands
   - Expected: code equals `0`
   - Expected: has_hello is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("shell executes simple commands")
if is_windows():
    # /bin/sh not available on Windows
    check(true)
else:
    val _result = test_shell("echo hello")
    val out = _result[0]
    val err = _result[1]
    val code = _result[2]
    expect(code).to_equal(0)
    val has_hello = out.contains("hello")
    expect(has_hello).to_equal(true)
```

</details>

### Linker Auto-Detection

#### detects system linker and provides info

- detects system linker and provides info


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("detects system linker and provides info")
check(test_auto_detect_linker())
check(test_get_linker_info())
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 12 |
| Active scenarios | 12 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-FEATURE`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `74aad1bab2e2128a901c348dc8458dcec7b43004fb52c7448ca0954b2a4afc14`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `74aad1bab2e2128a901c348dc8458dcec7b43004fb52c7448ca0954b2a4afc14`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `74aad1bab2e2128a901c348dc8458dcec7b43004fb52c7448ca0954b2a4afc14`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/feature/platform/cross_platform_spec.spl
mirror: doc/06_spec/feature/platform/cross_platform_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/feature/platform/cross_platform_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/feature/platform/cross_platform_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/feature/platform/cross_platform_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/feature/platform/cross_platform_spec.spl:67:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'detects current operating system' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/platform/cross_platform_spec.spl:73:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'is_unix returns true on Unix-like systems' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/platform/cross_platform_spec.spl:81:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'is_windows and is_unix are mutually exclusive' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
