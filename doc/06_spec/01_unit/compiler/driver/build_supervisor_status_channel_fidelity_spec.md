# A supervisor's status channel must preserve signal identity

> `build_outcome.spl` classifies a unit's fate from a wait status, and the whole

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# A supervisor's status channel must preserve signal identity

`build_outcome.spl` classifies a unit's fate from a wait status, and the whole

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler / driver |
| Status | Defect-CLASS detector (class-level twin of |
| Source | `test/01_unit/compiler/driver/build_supervisor_status_channel_fidelity_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and Audience

`build_outcome.spl` classifies a unit's fate from a wait status, and the whole
value of that classification rests on an assumption nobody had checked:

> **that the status the supervisor reads still says WHICH signal killed the
> child.**

Collapse that and the categories collapse with it. 139 (SIGSEGV, a compiler
crash), 137 (SIGKILL/OOM, a compiler crash) and 143 (SIGTERM from `earlyoom`,
infrastructure — UNVERIFIED, explicitly *not* a failure) all become one
indistinguishable value, and `build_outcome_classify_status` dutifully files all
three under the same category. The build then either invents compiler bugs out of
earlyoom kills, or hides real segfaults as "unverified". Both have happened in
this repo.

This is a defect CLASS, not one call site: it recurs at every boundary where a
child's fate crosses into the supervisor — `shell()`, a spawn/wait pair, a job
server, a `timeout` wrapper, a log line that got parsed back. Each is a fresh
opportunity to lose the signal, and losing it is silent.

The audience is anyone wiring a new process-launch path into the build.

## Scope and Preconditions

The detector is a contract over a *channel* — anything that turns "run this
command" into a status the supervisor will classify:

1. **Fidelity** — three different fatal signals must yield three different
   statuses.
2. **Correct categories** — those statuses must land as CRASHED, CRASHED and
   TERMINATED respectively, keeping the compiler's crashes disjoint from the
   host's interference.
3. **Ordinary exits unharmed** — a clean 0 and a diagnostic non-zero must still
   read OK and ERROR.

Two channels are measured. This is what gives the detector teeth: a check that
passes on everything it is pointed at detects nothing.

- **wrapped** — `sh -c '<cmd>'; rc=$?; exit $rc`, the form the poisoned-fixture
  harness uses. The inner shell dies by the signal; the outer shell reports the
  POSIX `128+N` value as its own ordinary exit code.
- **raw** — the command handed straight to `shell()`
  (`std.nogc_sync_mut.io.process_ops`).

**Measured, and the reason this spec exists:** the raw channel reports `-1` for
*every* signal death. SIGSEGV, SIGKILL and SIGTERM are indistinguishable through
it. That is not a hypothetical — it is why the fixture harness wraps.

## Expected Outcome

The wrapped channel satisfies all three clauses. The raw channel is asserted to
FAIL clause 1, which is simultaneously the proof that the detector discriminates
and the record of the live defect. When the raw channel is one day fixed to
preserve `128+N`, the final example here goes red on purpose and should be
flipped to expect fidelity — a detector that could not notice that would be
worthless.

## Scenarios

### the supervisor's status channel preserves signal identity

#### gives three different fatal signals three different statuses

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- gives three different fatal signals three different statuses


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("gives three different fatal signals three different statuses")
assert_true(channel_preserves_signal_identity(true))
```

</details>

#### reports the exact POSIX 128+N status for each signal

- reports the exact POSIX 128+N status for each signal
   - Expected: status_via_wrapped_channel("kill -SEGV $$") equals `139`
   - Expected: status_via_wrapped_channel("kill -KILL $$") equals `137`
   - Expected: status_via_wrapped_channel("kill -TERM $$") equals `143`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("reports the exact POSIX 128+N status for each signal")
expect(status_via_wrapped_channel("kill -SEGV $$")).to_equal(139)
expect(status_via_wrapped_channel("kill -KILL $$")).to_equal(137)
expect(status_via_wrapped_channel("kill -TERM $$")).to_equal(143)
```

</details>

### preserved statuses land in disjoint outcome categories

#### keeps a compiler crash apart from host interference

- keeps a compiler crash apart from host interference
   - Expected: build_outcome_kind_label(segv) equals `CRASHED`
   - Expected: build_outcome_kind_label(oom) equals `CRASHED`
   - Expected: build_outcome_kind_label(term) equals `TERMINATED`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("keeps a compiler crash apart from host interference")
val segv = build_outcome_classify_status(
    status_via_wrapped_channel("kill -SEGV $$"), false)
val oom = build_outcome_classify_status(
    status_via_wrapped_channel("kill -KILL $$"), false)
val term = build_outcome_classify_status(
    status_via_wrapped_channel("kill -TERM $$"), false)
expect(build_outcome_kind_label(segv)).to_equal("CRASHED")
expect(build_outcome_kind_label(oom)).to_equal("CRASHED")
# 143 is earlyoom, not the compiler. Filing it as CRASHED manufactures a
# phantom compiler bug; filing a real SIGSEGV as TERMINATED hides one.
expect(build_outcome_kind_label(term)).to_equal("TERMINATED")
```

</details>

#### leaves ordinary exits classified as before

- leaves ordinary exits classified as before


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("leaves ordinary exits classified as before")
expect(build_outcome_kind_label(
    build_outcome_classify_status(status_via_wrapped_channel("true"), false)))
    .to_equal("OK")
expect(build_outcome_kind_label(
    build_outcome_classify_status(status_via_wrapped_channel("exit 3"), false)))
    .to_equal("ERROR")
```

</details>

#### lets a budget kill outrank the signal that enforced it

- lets a budget kill outrank the signal that enforced it


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("lets a budget kill outrank the signal that enforced it")
# A unit killed on its own budget is TIMEOUT even though the enforcing
# signal was a SIGKILL that would otherwise read CRASHED(137).
expect(build_outcome_kind_label(build_outcome_classify_status(137, true)))
    .to_equal("TIMEOUT")
```

</details>

### the detector discriminates between a faithful and a lossy channel

#### fails the raw runtime channel, which collapses every signal to one value

- fails the raw runtime channel, which collapses every signal to one value


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("fails the raw runtime channel, which collapses every signal to one value")
# THE CONTROL. If this passed too, the detector above would prove
# nothing. `shell()` returns -1 for SIGSEGV, SIGKILL and SIGTERM alike,
# so all three would classify identically (ERROR, since -1 is not 128+N).
assert_false(channel_preserves_signal_identity(false))
expect(status_via_raw_channel("kill -SEGV $$"))
    .to_equal(status_via_raw_channel("kill -TERM $$"))
```

</details>

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
- `REQ-DRIVER-BUILD-OUTCOME-004`
- `REQ-SSPEC-COMPILER`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `c3dff8e55e0871bba11503eee4da8b4da3939dee802ec34c94750911218633a8`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `c3dff8e55e0871bba11503eee4da8b4da3939dee802ec34c94750911218633a8`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `c3dff8e55e0871bba11503eee4da8b4da3939dee802ec34c94750911218633a8`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **80/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/01_unit/compiler/driver/build_supervisor_status_channel_fidelity_spec.spl
mirror: doc/06_spec/01_unit/compiler/driver/build_supervisor_status_channel_fidelity_spec.md (current)
findings: 7 blockers: 1
  narrative=100 structure=100 oracle=70
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=80; blocker cap makes effective=49
doc/06_spec/01_unit/compiler/driver/build_supervisor_status_channel_fidelity_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/driver/build_supervisor_status_channel_fidelity_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/driver/build_supervisor_status_channel_fidelity_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 3 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/driver/build_supervisor_status_channel_fidelity_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 2 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/compiler/driver/build_supervisor_status_channel_fidelity_spec.spl:113:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'gives three different fatal signals three different statuses' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/driver/build_supervisor_status_channel_fidelity_spec.spl:118:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reports the exact POSIX 128+N status for each signal' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/driver/build_supervisor_status_channel_fidelity_spec.spl:126:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps a compiler crash apart from host interference' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
