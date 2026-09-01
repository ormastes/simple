# Io Runtime Import Specification

> Tests covering std.io_runtime imports.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Io Runtime Import Specification

## Scenarios

### std.io_runtime imports

<details>
<summary>Advanced: shell returns ShellResult</summary>

#### shell returns ShellResult _(slow)_

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- shell returns ShellResult
   - Expected: result.exit_code equals `0`
   - Expected: result.stdout.trim() equals `hello`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("shell returns ShellResult")
val result = shell("echo hello")
expect(result.exit_code).to_equal(0)
expect(result.stdout.trim()).to_equal("hello")
```

</details>


</details>

<details>
<summary>Advanced: shell_output returns trimmed stdout</summary>

#### shell_output returns trimmed stdout _(slow)_

- shell_output returns trimmed stdout
   - Expected: out equals `world`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("shell_output returns trimmed stdout")
val out = shell_output("echo world")
expect(out).to_equal("world")
```

</details>


</details>

<details>
<summary>Advanced: shell_bool returns bool</summary>

#### shell_bool returns bool _(slow)_

- shell_bool returns bool
   - Expected: shell_bool("true") is true
   - Expected: shell_bool("false") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("shell_bool returns bool")
expect(shell_bool("true")).to_equal(true)
expect(shell_bool("false")).to_equal(false)
```

</details>


</details>

<details>
<summary>Advanced: file_write and file_read round-trip</summary>

#### file_write and file_read round-trip _(slow)_

- file_write and file_read round-trip
   - Expected: content.trim() equals `hello io_runtime`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("file_write and file_read round-trip")
val path = "/tmp/io_runtime_test_{cwd().len()}.txt"
file_write(path, "hello io_runtime")
val content = file_read(path)
expect(content.trim()).to_equal("hello io_runtime")
file_delete(path)
```

</details>


</details>

<details>
<summary>Advanced: file_exists works</summary>

#### file_exists works _(slow)_

- file_exists works
   - Expected: file_exists("/tmp") is true
   - Expected: file_exists("/tmp/nonexistent_io_runtime_test_xyz") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("file_exists works")
expect(file_exists("/tmp")).to_equal(true)
expect(file_exists("/tmp/nonexistent_io_runtime_test_xyz")).to_equal(false)
```

</details>


</details>

<details>
<summary>Advanced: env_get and env_set work</summary>

#### env_get and env_set work _(slow)_

- env_get and env_set work
   - Expected: v equals `test_value`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("env_get and env_set work")
env_set("IO_RUNTIME_TEST_VAR", "test_value")
val v = env_get("IO_RUNTIME_TEST_VAR")
expect(v).to_equal("test_value")
```

</details>


</details>

<details>
<summary>Advanced: cwd returns non-empty</summary>

#### cwd returns non-empty _(slow)_

- cwd returns non-empty
   - Expected: has_content is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("cwd returns non-empty")
val dir = cwd()
val has_content = dir.len() > 0
expect(has_content).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: host_os returns known value</summary>

#### host_os returns known value _(slow)_

- host_os returns known value
   - Expected: is_known is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("host_os returns known value")
val os = host_os()
val is_known = os == "linux" or os == "macos" or os == "freebsd"
expect(is_known).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: host_arch returns known value</summary>

#### host_arch returns known value _(slow)_

- host_arch returns known value
   - Expected: is_known is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("host_arch returns known value")
val arch = host_arch()
val is_known = arch == "x86_64" or arch == "aarch64" or arch == "armv7" or arch == "riscv64" or arch == "riscv32"
expect(is_known).to_equal(true)
```

</details>


</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/integration/app/io_runtime_import_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering std.io_runtime imports.
- std.io_runtime imports

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
| Slow scenarios | 9 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-INTEGRATION`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `c317edab736ed32c5313383382469b2c6f5b7138fbef871f27139b3023721113`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `c317edab736ed32c5313383382469b2c6f5b7138fbef871f27139b3023721113`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `c317edab736ed32c5313383382469b2c6f5b7138fbef871f27139b3023721113`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/integration/app/io_runtime_import_spec.spl
mirror: doc/06_spec/integration/app/io_runtime_import_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/integration/app/io_runtime_import_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/integration/app/io_runtime_import_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/integration/app/io_runtime_import_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/integration/app/io_runtime_import_spec.spl:14:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'shell returns ShellResult' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/app/io_runtime_import_spec.spl:21:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'shell_output returns trimmed stdout' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/app/io_runtime_import_spec.spl:27:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'shell_bool returns bool' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
