# @manual: primary

> Purpose: Prove that tier-1 facilities report their true status.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 19 | 19 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# @manual: primary

Purpose: Prove that tier-1 facilities report their true status.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/posix/posix_server_contract_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Prove that tier-1 facilities report their true status.
Audience: compiler and tooling engineers who maintain this spec.
## Operator workflow
Run this spec with the test runner and read the per-scenario verdict lines;
a failing scenario pinpoints the behavior that regressed.
## Compatibility and limitations
Covers the pinned behavior only; fixture data is local to this spec.
# @manual: primary
REQ-OS-POSIX-001
doc/01_research/local/REQ-OS-POSIX-001.md
doc/03_plan/sys_test/REQ-OS-POSIX-001.md
doc/04_architecture/REQ-OS-POSIX-001.md
doc/05_design/REQ-OS-POSIX-001.md

## Scenarios

### tier-1 facilities report their true status

#### posix_spawn is supported

- Verify: posix_spawn is supported
   - Expected: facility_status("posix_spawn") equals `supported`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-POSIX-001
step("Verify: posix_spawn is supported")
expect(facility_status("posix_spawn")).to_equal("supported")
```

</details>

#### execve is supported

- Verify: execve is supported
   - Expected: facility_status("execve") equals `supported`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-POSIX-001
step("Verify: execve is supported")
expect(facility_status("execve")).to_equal("supported")
```

</details>

#### waitpid is supported

- Verify: waitpid is supported
   - Expected: facility_status("waitpid") equals `supported`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-POSIX-001
step("Verify: waitpid is supported")
expect(facility_status("waitpid")).to_equal("supported")
```

</details>

#### fork is only partial (no copy-on-write fork yet)

- Verify: fork is only partial (no copy-on-write fork yet)
   - Expected: facility_status("fork") equals `partial`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-POSIX-001
step("Verify: fork is only partial (no copy-on-write fork yet)")
expect(facility_status("fork")).to_equal("partial")
```

</details>

#### signals, dup2, pipe, poll, select are supported

- Verify: signals, dup2, pipe, poll, select are supported
   - Expected: facility_status("signals") equals `supported`
   - Expected: facility_status("dup2") equals `supported`
   - Expected: facility_status("pipe") equals `supported`
   - Expected: facility_status("poll") equals `supported`
   - Expected: facility_status("select") equals `supported`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-POSIX-001
step("Verify: signals, dup2, pipe, poll, select are supported")
expect(facility_status("signals")).to_equal("supported")
expect(facility_status("dup2")).to_equal("supported")
expect(facility_status("pipe")).to_equal("supported")
expect(facility_status("poll")).to_equal("supported")
expect(facility_status("select")).to_equal("supported")
```

</details>

### unimplemented facilities fail closed, never fake success

#### af_unix_socketpair reports unsupported (not fake-supported)

- Verify: af_unix_socketpair reports unsupported (not fake-supported)
   - Expected: facility_status("af_unix_socketpair") equals `unsupported`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-POSIX-001
step("Verify: af_unix_socketpair reports unsupported (not fake-supported)")
expect(facility_status("af_unix_socketpair")).to_equal("unsupported")
```

</details>

#### process_groups reports unsupported

- Verify: process_groups reports unsupported
   - Expected: facility_status("process_groups") equals `unsupported`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-POSIX-001
step("Verify: process_groups reports unsupported")
expect(facility_status("process_groups")).to_equal("unsupported")
```

</details>

#### an unknown facility fails closed to unsupported

- Verify: an unknown facility fails closed to unsupported
   - Expected: facility_status("no_such_call") equals `unsupported`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-POSIX-001
step("Verify: an unknown facility fails closed to unsupported")
expect(facility_status("no_such_call")).to_equal("unsupported")
```

</details>

#### the honesty invariant holds: no unimplemented facility reports supported

- machine-check the fail-closed rule across the whole table
   - Expected: honesty_violations().len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-POSIX-001
step("machine-check the fail-closed rule across the whole table")
expect(honesty_violations().len()).to_equal(0)  # oracle: 0 — named expected value from the requirement
```

</details>

#### gives an honest reason for the AF_UNIX gap

- Verify: gives an honest reason for the AF_UNIX gap


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-POSIX-001
step("Verify: gives an honest reason for the AF_UNIX gap")
expect(facility_reason("af_unix_socketpair")).to_contain("AF_UNIX")
```

</details>

### section 9.3 order is a real can_enable constraint

#### poll is denied before the full-FD-semantics tier (dup2) is enabled

- enabled through process_groups but NOT dup2
   - Expected: can_enable("poll", without_fd) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-POSIX-001
step("enabled through process_groups but NOT dup2")
val without_fd: [text] = ["posix_spawn", "execve", "waitpid", "signals", "process_groups"]
expect(can_enable("poll", without_fd)).to_equal(false)
```

</details>

#### poll is allowed once dup2 is enabled

- Verify: poll is allowed once dup2 is enabled
   - Expected: can_enable("poll", with_fd) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-POSIX-001
step("Verify: poll is allowed once dup2 is enabled")
val with_fd: [text] = ["dup2"]
expect(can_enable("poll", with_fd)).to_equal(true)
```

</details>

#### af_unix_socketpair is also gated behind dup2

- Verify: af_unix_socketpair is also gated behind dup2
   - Expected: can_enable("af_unix_socketpair", without_fd) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-POSIX-001
step("Verify: af_unix_socketpair is also gated behind dup2")
val without_fd: [text] = ["posix_spawn", "execve", "waitpid", "signals"]
expect(can_enable("af_unix_socketpair", without_fd)).to_equal(false)
```

</details>

#### tier-1 roots (posix_spawn) have no prerequisites and always enable

- Verify: tier-1 roots (posix_spawn) have no prerequisites and always enable
   - Expected: prerequisites("posix_spawn").len() equals `0`
   - Expected: can_enable("posix_spawn", empty) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-POSIX-001
step("Verify: tier-1 roots (posix_spawn) have no prerequisites and always enable")
val empty: [text] = []
expect(prerequisites("posix_spawn").len()).to_equal(0)
expect(can_enable("posix_spawn", empty)).to_equal(true)
```

</details>

#### poll's prerequisite set names dup2

- Verify: poll's prerequisite set names dup2
   - Expected: list_contains(prerequisites("poll"), "dup2") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-POSIX-001
step("Verify: poll's prerequisite set names dup2")
expect(list_contains(prerequisites("poll"), "dup2")).to_equal(true)
```

</details>

### profile supported sets differ across profiles

#### Profile A native exposes none of the POSIX tier-1 adapter symbols

- Verify: Profile A native exposes none of the POSIX tier-1 adapter symbols
   - Expected: profile_supported_set("A").len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-POSIX-001
step("Verify: Profile A native exposes none of the POSIX tier-1 adapter symbols")
expect(profile_supported_set("A").len()).to_equal(0)
```

</details>

#### Profile C POSIX-server exposes a non-empty supported set

- Verify: Profile C POSIX-server exposes a non-empty supported set


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-POSIX-001
step("Verify: Profile C POSIX-server exposes a non-empty supported set")
expect(profile_supported_set("C").len()).to_be_greater_than(0)
```

</details>

#### Profile A set differs in size from Profile C set

- Verify: Profile A set differs in size from Profile C set
   - Expected: a.len() == c.len() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-POSIX-001
step("Verify: Profile A set differs in size from Profile C set")
val a = profile_supported_set("A")
val c = profile_supported_set("C")
expect(a.len() == c.len()).to_equal(false)
```

</details>

#### Profile C includes waitpid but not the unsupported af_unix_socketpair

- Verify: Profile C includes waitpid but not the unsupported af_unix_socketpair
   - Expected: list_contains(c, "waitpid") is true
   - Expected: list_contains(c, "af_unix_socketpair") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-POSIX-001
step("Verify: Profile C includes waitpid but not the unsupported af_unix_socketpair")
val c = profile_supported_set("C")
expect(list_contains(c, "waitpid")).to_equal(true)
expect(list_contains(c, "af_unix_socketpair")).to_equal(false)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 19 |
| Active scenarios | 19 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
- `REQ-OS-POSIX-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `18cc938d85df2ecfa93cc155417a3c47a9c7ef95c234db3704ab77c22fe38fa2`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `18cc938d85df2ecfa93cc155417a3c47a9c7ef95c234db3704ab77c22fe38fa2`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `18cc938d85df2ecfa93cc155417a3c47a9c7ef95c234db3704ab77c22fe38fa2`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **82/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/01_unit/os/posix/posix_server_contract_spec.spl
mirror: doc/06_spec/01_unit/os/posix/posix_server_contract_spec.md (current)
findings: 7 blockers: 1
  narrative=100 structure=100 oracle=80
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=82; blocker cap makes effective=49
doc/06_spec/01_unit/os/posix/posix_server_contract_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/os/posix/posix_server_contract_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, evidence, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/os/posix/posix_server_contract_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/os/posix/posix_server_contract_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 1 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/os/posix/posix_server_contract_spec.spl:60:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'posix_spawn is supported' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/posix/posix_server_contract_spec.spl:65:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'execve is supported' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/posix/posix_server_contract_spec.spl:70:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'waitpid is supported' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
