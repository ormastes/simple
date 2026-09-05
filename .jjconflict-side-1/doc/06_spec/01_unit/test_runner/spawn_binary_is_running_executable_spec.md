# Spawn Binary Is Running Executable Specification

> Tests covering cli_get_args() does not report the executable — the defect's premise, find_simple_binary — reproducing case, defect class — self-exe resolution invariants.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Spawn Binary Is Running Executable Specification

## Scenarios

### cli_get_args() does not report the executable — the defect's premise

#### never yields a path that ends in /simple as argv[0]

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- never yields a path that ends in /simple as argv[0]


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("never yields a path that ends in /simple as argv[0]")
# This is the observation that invalidates the argv[0] branch. If this
# ever becomes false the branch starts working and this spec should be
# revisited — but it must never be the ONLY thing standing between a
# measurement and the wrong binary.
val args = cli_get_args()
if args.len() > 0:
    assert_false(args[0].ends_with("/simple"))
```

</details>

### find_simple_binary — reproducing case

#### resolves to a real, existing executable, not an unresolvable literal

- resolves to a real, existing executable, not an unresolvable literal


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("resolves to a real, existing executable, not an unresolvable literal")
val binary = find_simple_binary()
assert_true(binary != "")
# Pre-fix this returned the literal "bin/simple" even when the running
# binary lived elsewhere. The point of the assertion is that whatever
# comes back must actually exist on disk from the current working
# directory, so a spawn cannot silently fail or hit a stale build.
assert_true(file_exists(binary))
```

</details>

#### prefers the running executable over the deployed bin/simple path

- prefers the running executable over the deployed bin/simple path


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("prefers the running executable over the deployed bin/simple path")
# On any host with /proc, resolution must land on the CANONICALISED
# self-exe path — an absolute path, never the literal link. Handing the
# link itself to the spawner made every child exit 125, because the
# children are launched via `timeout ... <binary> run <spec>` and
# /proc/self/exe there belongs to `timeout`.
if file_exists("/proc/self/exe"):
    val resolved = find_simple_binary()
    assert_true(resolved.starts_with("/"))
    assert_false(resolved.contains("/proc/self/exe"))
    assert_true(resolved.ends_with("/simple"))
```

</details>

### defect class — self-exe resolution invariants

#### returns a stable answer across repeated calls

- returns a stable answer across repeated calls


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns a stable answer across repeated calls")
# `_cached_binary_path` memoizes the first answer; a first call that
# resolved wrongly poisons every later spawn in the process.
val first = find_simple_binary()
assert_equal(find_simple_binary(), first)
assert_equal(find_simple_binary(), first)
```

</details>

#### positive control: the self-exe link exists and is usable where /proc is present

- positive control: the self-exe link exists and is usable where /proc is present


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("positive control: the self-exe link exists and is usable where /proc is present")
# Guards against the fix degenerating into a vacuous branch: if this
# control ever fails on Linux, the resolution above is falling through
# to the candidate list again.
if file_exists("/proc/version"):
    assert_true(file_exists("/proc/self/exe"))
```

</details>

#### positive control: an obviously absent path is still reported absent

- positive control: an obviously absent path is still reported absent


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("positive control: an obviously absent path is still reported absent")
# Proves file_exists is discriminating, so the assertions above are not
# trivially true.
assert_false(file_exists("/proc/self/definitely-not-an-exe-link"))
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/01_unit/test_runner/spawn_binary_is_running_executable_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering cli_get_args() does not report the executable — the defect's premise, find_simple_binary — reproducing case, defect class — self-exe resolution invariants.
- cli_get_args() does not report the executable — the defect's premise
- find_simple_binary — reproducing case
- defect class — self-exe resolution invariants

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
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

- Canonical SPipe generation for source `d57fbba3a404551deea57578676785e784de3dfcba8e54461793de3805200991`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `d57fbba3a404551deea57578676785e784de3dfcba8e54461793de3805200991`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `d57fbba3a404551deea57578676785e784de3dfcba8e54461793de3805200991`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/test_runner/spawn_binary_is_running_executable_spec.spl
mirror: doc/06_spec/01_unit/test_runner/spawn_binary_is_running_executable_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/test_runner/spawn_binary_is_running_executable_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/test_runner/spawn_binary_is_running_executable_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/test_runner/spawn_binary_is_running_executable_spec.spl:25:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'never yields a path that ends in /simple as argv[0]' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/test_runner/spawn_binary_is_running_executable_spec.spl:37:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'resolves to a real, existing executable, not an unresolvable literal' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/test_runner/spawn_binary_is_running_executable_spec.spl:48:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'prefers the running executable over the deployed bin/simple path' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
