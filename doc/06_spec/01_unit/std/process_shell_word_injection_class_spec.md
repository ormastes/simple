# Process Shell Word Injection Class Specification

> Tests covering shell-word quoting on the resource-limited process path (class).

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Process Shell Word Injection Class Specification

## Scenarios

### shell-word quoting on the resource-limited process path (class)

#### POSITIVE CONTROL: the subject module loads and actually runs a child

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- POSITIVE CONTROL: the subject module loads and actually runs a child


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("POSITIVE CONTROL: the subject module loads and actually runs a child")
# Proves process_ops is really imported and really execs, so that a
# green result below cannot come from a module that never loaded.
val (stdout, stderr, code) = process_run("/bin/echo", ["subject-alive"])
assert_equal(code, 0)
assert_contains(stdout, "subject-alive")
```

</details>

#### POSITIVE CONTROL: the limited path also really runs a child

- POSITIVE CONTROL: the limited path also really runs a child


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("POSITIVE CONTROL: the limited path also really runs a child")
val r = process_run_with_limits("/bin/echo", ["limited-alive"], 5000, 0, 0, 0, 0)
assert_equal(r.exit_code, 0)
assert_contains(r.stdout, "limited-alive")
```

</details>

#### installs an executable whose path holds space, ; $ backtick and quote

- installs an executable whose path holds space, ; $ backtick and quote


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("installs an executable whose path holds space, ; $ backtick and quote")
_install()
assert_equal(file_exists(_exe()), true)
```

</details>

#### runs a command word full of shell metacharacters verbatim

- runs a command word full of shell metacharacters verbatim


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("runs a command word full of shell metacharacters verbatim")
_install()
val r = process_run_with_limits(_exe(), ["payload"], 5000, 0, 0, 0, 0)
assert_equal(r.exit_code, 0)
assert_contains(r.stdout, "OK:payload")
```

</details>

#### POSITIVE CONTROL: the canary path is really creatable and removable

- POSITIVE CONTROL: the canary path is really creatable and removable


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("POSITIVE CONTROL: the canary path is really creatable and removable")
# Without this, the two "canary was not created" examples below could
# pass simply because touch is missing or the directory is unwritable.
val _ = dir_create_all(_dir())
val t = process_run("/usr/bin/touch", [_canary()])
assert_equal(t.2, 0)
assert_equal(file_exists(_canary()), true)
val rm = process_run("/bin/rm", ["-f", _canary()])
assert_equal(rm.2, 0)
assert_equal(file_exists(_canary()), false)
```

</details>

#### does not let a metacharacter in the command word execute a side effect

- does not let a metacharacter in the command word execute a side effect


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does not let a metacharacter in the command word execute a side effect")
# If the command word were interpolated raw, the embedded `;` would
# start a second shell command. Point that at a canary file and prove
# it was never created.
val _ = dir_create_all(_dir())
val injected = "/bin/echo ok ; /usr/bin/touch '{_canary()}' ; /bin/true"
val r = process_run_with_limits(injected, [], 5000, 0, 0, 0, 0)
assert_equal(file_exists(_canary()), false)
```

</details>

#### does not let a metacharacter in an ARGUMENT execute a side effect

- does not let a metacharacter in an ARGUMENT execute a side effect


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does not let a metacharacter in an ARGUMENT execute a side effect")
val _ = dir_create_all(_dir())
val injected_arg = "; /usr/bin/touch '{_canary()}' ;"
val r = process_run_with_limits("/bin/echo", [injected_arg], 5000, 0, 0, 0, 0)
assert_equal(r.exit_code, 0)
assert_equal(file_exists(_canary()), false)
```

</details>

#### passes an embedded single quote through as data

- passes an embedded single quote through as data


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("passes an embedded single quote through as data")
val r = process_run_with_limits("/bin/echo", ["it's fine"], 5000, 0, 0, 0, 0)
assert_equal(r.exit_code, 0)
assert_contains(r.stdout, "it's fine")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/std/process_shell_word_injection_class_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering shell-word quoting on the resource-limited process path (class).
- shell-word quoting on the resource-limited process path (class)

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
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

- Canonical SPipe generation for source `57b5bbe4db83d4c79d746fedbf3c4828adc70c99d7262ca189218386c52bfd17`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `57b5bbe4db83d4c79d746fedbf3c4828adc70c99d7262ca189218386c52bfd17`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `57b5bbe4db83d4c79d746fedbf3c4828adc70c99d7262ca189218386c52bfd17`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/std/process_shell_word_injection_class_spec.spl
mirror: doc/06_spec/01_unit/std/process_shell_word_injection_class_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/std/process_shell_word_injection_class_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/std/process_shell_word_injection_class_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/std/process_shell_word_injection_class_spec.spl:41:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'POSITIVE CONTROL: the subject module loads and actually runs a child' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/std/process_shell_word_injection_class_spec.spl:50:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'POSITIVE CONTROL: the limited path also really runs a child' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/std/process_shell_word_injection_class_spec.spl:57:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'installs an executable whose path holds space, ; $ backtick and quote' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
