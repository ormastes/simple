# coreutils/kill argument parsing + signal parser

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 14 | 14 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# coreutils/kill argument parsing + signal parser

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #WAVE5-G9 |
| Category | Userland coreutils |
| Status | Active |
| Source | `test/unit/os/apps/coreutils/kill_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Scenarios

### parse_signal

#### -9 is SIGKILL

- -9 is SIGKILL


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("-9 is SIGKILL")
expect parse_signal("-9").to_equal(9i32)
```

</details>

#### -15 is SIGTERM

- -15 is SIGTERM


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("-15 is SIGTERM")
expect parse_signal("-15").to_equal(15i32)
```

</details>

#### -SIGINT is 2

- -SIGINT is 2


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("-SIGINT is 2")
expect parse_signal("-SIGINT").to_equal(2i32)
```

</details>

#### -SIGTERM is 15

- -SIGTERM is 15


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("-SIGTERM is 15")
expect parse_signal("-SIGTERM").to_equal(15i32)
```

</details>

#### unknown signal returns -1

- unknown signal returns -1


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("unknown signal returns -1")
expect parse_signal("-BOGUS").to_equal(-1i32)
```

</details>

#### empty string returns -1

- empty string returns -1


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("empty string returns -1")
expect parse_signal("").to_equal(-1i32)
```

</details>

#### missing leading dash returns -1

- missing leading dash returns -1


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("missing leading dash returns -1")
expect parse_signal("9").to_equal(-1i32)
```

</details>

### parse_pid
_Pid decimal parser._

#### parses '42' as 42

- parses '42' as 42


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses '42' as 42")
expect parse_pid("42").to_equal(42i64)
```

</details>

#### rejects empty string

- rejects empty string


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects empty string")
expect parse_pid("").to_equal(-1i64)
```

</details>

#### rejects non-digit

- rejects non-digit


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects non-digit")
expect parse_pid("abc").to_equal(-1i64)
```

</details>

### main_kill argument parsing
_Entry-point argument handling._

#### no args returns 1

- no args returns 1


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("no args returns 1")
"""kill with nothing must complain."""
val rc = main_kill([])
expect rc.to_equal(1i32)
```

</details>

#### --help returns 0

- --help returns 0


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("--help returns 0")
"""Help is a no-op successful exit."""
val rc = main_kill(["--help"])
expect rc.to_equal(0i32)
```

</details>

#### only signal flag + missing pid returns 1

- only signal flag + missing pid returns 1


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("only signal flag + missing pid returns 1")
"""kill -9 with no pid is a usage error."""
val rc = main_kill(["-9"])
expect rc.to_equal(1i32)
```

</details>

#### unknown signal returns 1

- unknown signal returns 1


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("unknown signal returns 1")
"""Unknown -FOO must be a usage error."""
val rc = main_kill(["-FOO", "1"])
expect rc.to_equal(1i32)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 14 |
| Active scenarios | 14 |
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

- Canonical SPipe generation for source `cc945989284d316acd44988fe98afa85a540650d0f79cc7a9eb4de53b1f30eee`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `cc945989284d316acd44988fe98afa85a540650d0f79cc7a9eb4de53b1f30eee`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `cc945989284d316acd44988fe98afa85a540650d0f79cc7a9eb4de53b1f30eee`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/os/apps/coreutils/kill_spec.spl
mirror: doc/06_spec/unit/os/apps/coreutils/kill_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/os/apps/coreutils/kill_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/os/apps/coreutils/kill_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/os/apps/coreutils/kill_spec.spl:19:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario '-9 is SIGKILL' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/os/apps/coreutils/kill_spec.spl:24:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario '-15 is SIGTERM' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/os/apps/coreutils/kill_spec.spl:29:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario '-SIGINT is 2' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
