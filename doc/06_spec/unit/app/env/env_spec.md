# Env Specification

> Tests covering Environment Variables, Platform Detection, Configuration Sources, Build Environment.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 15 | 15 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Env Specification

## Scenarios

### Environment Variables

#### HOME is set and non-empty

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- HOME is set and non-empty
   - Expected: home != "" is true
   - Expected: home.starts_with("/") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("HOME is set and non-empty")
val home = env_val("HOME")
expect(home != "").to_equal(true)
expect(home.starts_with("/")).to_equal(true)
```

</details>

#### PATH is set and contains separator

- PATH is set and contains separator
   - Expected: path != "" is true
   - Expected: path contains `":") or path`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("PATH is set and contains separator")
val path = env_val("PATH")
expect(path != "").to_equal(true)
expect(path.contains(":") or path.contains(";")).to_equal(true)
```

</details>

#### USER is set

- USER is set
   - Expected: user != "" is true
   - Expected: user.len() > 0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("USER is set")
val user = env_val("USER")
expect(user != "").to_equal(true)
expect(user.len() > 0).to_equal(true)
```

</details>

#### missing variable returns nil or empty

- missing variable returns nil or empty
   - Expected: is_empty is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("missing variable returns nil or empty")
val missing = rt_env_get("__SIMPLE_TEST_NONEXISTENT_VAR_XYZ__")
val is_empty = missing == nil or missing == ""
expect(is_empty).to_equal(true)
```

</details>

#### set and read back a variable

- set and read back a variable
   - Expected: readback equals `hello42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("set and read back a variable")
rt_env_set("__SIMPLE_TEST_ENV_ROUND_TRIP__", "hello42")
val readback = env_val("__SIMPLE_TEST_ENV_ROUND_TRIP__")
expect(readback).to_equal("hello42")
rt_env_remove("__SIMPLE_TEST_ENV_ROUND_TRIP__")
```

</details>

#### remove clears a variable

- remove clears a variable
   - Expected: gone is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("remove clears a variable")
rt_env_set("__SIMPLE_TEST_ENV_REMOVE__", "present")
rt_env_remove("__SIMPLE_TEST_ENV_REMOVE__")
val after = rt_env_get("__SIMPLE_TEST_ENV_REMOVE__")
val gone = after == nil or after == ""
expect(gone).to_equal(true)
```

</details>

### Platform Detection

#### uname returns a known OS

- uname returns a known OS
   - Expected: code equals `0`
   - Expected: known is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("uname returns a known OS")
val result = rt_process_run("/bin/sh", ["-c", "uname -s"])
val os_name = result[0].trim()
val code = result[2]
expect(code).to_equal(0)
val known = (os_name == "Linux" or os_name == "Darwin" or
    os_name == "FreeBSD" or os_name == "OpenBSD" or os_name == "NetBSD")
expect(known).to_equal(true)
```

</details>

#### uname -m returns a known architecture

- uname -m returns a known architecture
   - Expected: code equals `0`
   - Expected: arch.len() > 0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("uname -m returns a known architecture")
val result = rt_process_run("/bin/sh", ["-c", "uname -m"])
val arch = result[0].trim()
val code = result[2]
expect(code).to_equal(0)
expect(arch.len() > 0).to_equal(true)
```

</details>

#### PWD or working directory is accessible

- PWD or working directory is accessible
   - Expected: pwd != "" is true
   - Expected: pwd.starts_with("/") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("PWD or working directory is accessible")
val pwd = env_val("PWD")
expect(pwd != "").to_equal(true)
expect(pwd.starts_with("/")).to_equal(true)
```

</details>

### Configuration Sources

#### env var set takes precedence over missing

- env var set takes precedence over missing
   - Expected: value equals `from_env`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("env var set takes precedence over missing")
rt_env_set("__SIMPLE_TEST_PRIORITY__", "from_env")
val value = env_val("__SIMPLE_TEST_PRIORITY__")
expect(value).to_equal("from_env")
rt_env_remove("__SIMPLE_TEST_PRIORITY__")
```

</details>

#### missing env var falls back to default

- missing env var falls back to default
   - Expected: is_empty is true
   - Expected: fallback equals `default_value`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("missing env var falls back to default")
val raw = rt_env_get("__SIMPLE_TEST_MISSING_CONFIG__")
val is_empty = raw == nil or raw == ""
expect(is_empty).to_equal(true)
val fallback = if is_empty: "default_value" else: raw
expect(fallback).to_equal("default_value")
```

</details>

#### overwrite replaces previous value

- overwrite replaces previous value
   - Expected: value equals `second`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("overwrite replaces previous value")
rt_env_set("__SIMPLE_TEST_OVERWRITE__", "first")
rt_env_set("__SIMPLE_TEST_OVERWRITE__", "second")
val value = env_val("__SIMPLE_TEST_OVERWRITE__")
expect(value).to_equal("second")
rt_env_remove("__SIMPLE_TEST_OVERWRITE__")
```

</details>

### Build Environment

#### SHELL is set on unix

- SHELL is set on unix
   - Expected: has_shell is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("SHELL is set on unix")
val shell = env_val("SHELL")
val has_shell = shell != ""
expect(has_shell).to_equal(true)
```

</details>

#### LANG or LC variables exist

- LANG or LC variables exist
   - Expected: has_locale is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("LANG or LC variables exist")
val lang = env_val("LANG")
val lc_all = env_val("LC_ALL")
val has_locale = lang != "" or lc_all != ""
expect(has_locale).to_equal(true)
```

</details>

#### TERM is set in interactive sessions

- TERM is set in interactive sessions
   - Expected: has_term is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("TERM is set in interactive sessions")
val term = env_val("TERM")
val has_term = term != ""
expect(has_term).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/unit/app/env/env_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Environment Variables, Platform Detection, Configuration Sources, Build Environment.
- Environment Variables
- Platform Detection
- Configuration Sources
- Build Environment

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 15 |
| Active scenarios | 15 |
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

- Canonical SPipe generation for source `6397c331c4f852b0b96f56feb92197036d5109f48e5ea5d7785953a50fb33541`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `6397c331c4f852b0b96f56feb92197036d5109f48e5ea5d7785953a50fb33541`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `6397c331c4f852b0b96f56feb92197036d5109f48e5ea5d7785953a50fb33541`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/unit/app/env/env_spec.spl
mirror: doc/06_spec/unit/app/env/env_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/app/env/env_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/app/env/env_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/app/env/env_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/app/env/env_spec.spl:30:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'HOME is set and non-empty' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/env/env_spec.spl:37:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'PATH is set and contains separator' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/env/env_spec.spl:44:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'USER is set' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
