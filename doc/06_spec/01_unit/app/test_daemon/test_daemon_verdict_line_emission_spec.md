# test_daemon_verdict_line_emission_spec

> I run the test suite from automation, and the automation decides what is

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# test_daemon_verdict_line_emission_spec

I run the test suite from automation, and the automation decides what is

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/test_daemon/test_daemon_verdict_line_emission_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

I run the test suite from automation, and the automation decides what is
    broken by reading `SPEC FILE VERDICT:` lines -- not exit codes, because a
    directory run collapses hundreds of files into one exit code that cannot
    say WHICH file broke.

    So a spec file that never emits a verdict line is, to me, a file that was
    never run. That is not a cosmetic gap: 24 blink modules were missing for
    weeks and every sweep read the whole directory as "not yet written" instead
    of "broken", because the aggregating lane emitted zero verdict lines for
    all 24 files -- the passing ones too.

    What I need pinned is that a spec which CANNOT LOAD still produces a
    verdict line, and that the line says so loudly enough that I can tell an
    infrastructure gap from a failed assertion without reading the log.

## Scenarios

### every spec file a test run touches reports a machine-readable verdict

#### turns an unresolvable import into a verdict line marked unrun

- turns an unresolvable import into a verdict line marked unrun
- Take the compiler diagnostic a spec with a missing module produces
- Classify it and render the verdict line the runner would print
- The line must exist, name the file, and carry the unrun marker
   - Expected: reason equals `unresolved-module`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("turns an unresolvable import into a verdict line marked unrun")
step("Take the compiler diagnostic a spec with a missing module produces")
val diagnostic = "error: semantic: Cannot resolve module: std.blink.paint.paint_tree_walker"

step("Classify it and render the verdict line the runner would print")
val reason = unrun_reason(diagnostic)
val line = unrun_verdict_line("test/01_unit/lib/blink/paint_tree_walker_spec.spl", reason)

step("The line must exist, name the file, and carry the unrun marker")
expect(reason).to_equal("unresolved-module")
assert_true(has_verdict_line(line))
assert_contains(line, "test/01_unit/lib/blink/paint_tree_walker_spec.spl")
assert_contains(line, "unrun=1")
assert_contains(line, "reason=unresolved-module")
```

</details>

#### keeps an unloadable spec red under the dropped==0 greenwash gate

- keeps an unloadable spec red under the dropped==0 greenwash gate
- Render the verdict line for a spec that declared examples but loaded none
- Both halves of the load-bearing pair must be present


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("keeps an unloadable spec red under the dropped==0 greenwash gate")
"""
`executed=0` alone is ambiguous -- a spec that honestly declares no
examples also executed zero. `dropped=1` is what makes the gate refuse
to read this file as completed work.
"""
step("Render the verdict line for a spec that declared examples but loaded none")
val line = unrun_verdict_line("test/example_spec.spl", "unresolved-module")

step("Both halves of the load-bearing pair must be present")
assert_contains(line, "executed=0")
assert_contains(line, "dropped=1")
assert_contains(line, "failed=1")
```

</details>

#### names the cause so a sweep can route the file to the right owner

**Manual warnings:**
- invalid manual visibility metadata: # @manual_section Reasons separate infrastructure gaps from authoring gaps (expected show, folded, detail, or skip)


- names the cause so a sweep can route the file to the right owner
- A missing module is an infrastructure gap somebody must land
   - Expected: unrun_reason("error: semantic: Cannot resolve module: std.x.y") equals `unresolved-module`
- A parse error is a broken source file
   - Expected: unrun_reason("compile failed: parse: unexpected end of input") equals `parse-error`
- A spec that simply declares nothing is an authoring gap, not an outage
   - Expected: unrun_reason("Results: 0 total, 0 passed, 0 failed") equals `zero-examples`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("names the cause so a sweep can route the file to the right owner")
step("A missing module is an infrastructure gap somebody must land")
expect(unrun_reason("error: semantic: Cannot resolve module: std.x.y")).to_equal("unresolved-module")

step("A parse error is a broken source file")
expect(unrun_reason("compile failed: parse: unexpected end of input")).to_equal("parse-error")

step("A spec that simply declares nothing is an authoring gap, not an outage")
expect(unrun_reason("Results: 0 total, 0 passed, 0 failed")).to_equal("zero-examples")
```

</details>

#### treats only a load failure as a load failure

- treats only a load failure as a load failure
- A load diagnostic is a load failure
- A failed assertion is not


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("treats only a load failure as a load failure")
"""
A spec that ran and got the wrong answer must NOT be reported as
unloadable -- that would hide a real product defect behind an
infrastructure label.
"""
step("A load diagnostic is a load failure")
assert_true(is_load_failure("error: semantic: Cannot resolve module: std.x.y"))

step("A failed assertion is not")
assert_false(is_load_failure("expected 0 to equal 999"))
```

</details>

#### reports the executed counts for a spec the aggregating lane actually ran

**Manual warnings:**
- invalid manual visibility metadata: # @manual_section Specs that DID run report their real counts (expected show, folded, detail, or skip)


- reports the executed counts for a spec the aggregating lane actually ran
- Render the verdict line for a file that ran eight examples cleanly
- It must report the real counts and NOT claim anything was dropped
- A file that ran and failed reports its failures, still not dropped


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("reports the executed counts for a spec the aggregating lane actually ran")
"""
The directory lane emitted no verdict lines at all -- not just for
broken files. A passing file with no verdict line is equally invisible,
so the green case is pinned here too.
"""
step("Render the verdict line for a file that ran eight examples cleanly")
val line = ran_verdict_line("test/01_unit/lib/blink/url/url_parser_spec.spl", 8, 0)

step("It must report the real counts and NOT claim anything was dropped")
assert_true(has_verdict_line(line))
assert_contains(line, "executed=8")
assert_contains(line, "passed=8")
assert_contains(line, "failed=0")
assert_contains(line, "dropped=0")

step("A file that ran and failed reports its failures, still not dropped")
val red = ran_verdict_line("test/01_unit/lib/blink/css_selector_spec.spl", 0, 15)
assert_contains(red, "executed=15")
assert_contains(red, "failed=15")
assert_contains(red, "dropped=0")
```

</details>

#### keeps the timeout, unrun, and ran lines mutually distinguishable

- keeps the timeout, unrun, and ran lines mutually distinguishable
- Render one line of each kind
- Every one is a verdict line, and each carries its own marker


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("keeps the timeout, unrun, and ran lines mutually distinguishable")
"""
Three different reasons a file can end up in a report. A sweep must be
able to tell them apart from the line alone.
"""
step("Render one line of each kind")
val timed = timeout_verdict_line("test/a_spec.spl", "aggregate-lane-timeout", 600000)
val unrun = unrun_verdict_line("test/b_spec.spl", "unresolved-module")
val ran = ran_verdict_line("test/c_spec.spl", 3, 0)

step("Every one is a verdict line, and each carries its own marker")
assert_true(has_verdict_line(timed))
assert_true(has_verdict_line(unrun))
assert_true(has_verdict_line(ran))
assert_contains(timed, "timeout=1")
assert_contains(unrun, "unrun=1")
assert_false(ran.contains("unrun=1"))
assert_false(ran.contains("timeout=1"))
```

</details>

#### reports daemon no-response as inconclusive without fabricating a failed example

- reports daemon no-response as inconclusive without fabricating a failed example
- Render the verdict for a request whose daemon never answered
- Keep the infrastructure timeout visible without claiming execution or failure
- Keep a real worker timeout red and distinguishable


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("reports daemon no-response as inconclusive without fabricating a failed example")
step("Render the verdict for a request whose daemon never answered")
val line = no_response_verdict_line("test/slow_spec.spl", 840000)

step("Keep the infrastructure timeout visible without claiming execution or failure")
assert_true(has_verdict_line(line))
assert_contains(line, "executed=0")
assert_contains(line, "passed=0")
assert_contains(line, "failed=0")
assert_contains(line, "dropped=1")
assert_contains(line, "timeout=1")
assert_contains(line, "inconclusive=1")
assert_contains(line, "reason=daemon-no-response")
assert_contains(line, "budget_ms=840000")

step("Keep a real worker timeout red and distinguishable")
val worker = timeout_verdict_line("test/slow_spec.spl", "daemon-worker-timeout", 840000)
assert_contains(worker, "executed=1")
assert_contains(worker, "failed=1")
assert_false(worker.contains("inconclusive=1"))
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
- `REQ-TESTRUNNER-VERDICT-LINE`
- `REQ-SSPEC-APP`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `f51d390c7c9f7bf1e15da2368bb323d67ca87dcd726dee3da2899c79a26e76c1`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `f51d390c7c9f7bf1e15da2368bb323d67ca87dcd726dee3da2899c79a26e76c1`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `f51d390c7c9f7bf1e15da2368bb323d67ca87dcd726dee3da2899c79a26e76c1`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/01_unit/app/test_daemon/test_daemon_verdict_line_emission_spec.spl
mirror: doc/06_spec/01_unit/app/test_daemon/test_daemon_verdict_line_emission_spec.md (current)
findings: 6 blockers: 1
  narrative=100 structure=100 oracle=100
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=86; blocker cap makes effective=49
doc/06_spec/01_unit/app/test_daemon/test_daemon_verdict_line_emission_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/test_daemon/test_daemon_verdict_line_emission_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/test_daemon/test_daemon_verdict_line_emission_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 2 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/app/test_daemon/test_daemon_verdict_line_emission_spec.spl:34:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'turns an unresolvable import into a verdict line marked unrun' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/test_daemon/test_daemon_verdict_line_emission_spec.spl:51:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps an unloadable spec red under the dropped==0 greenwash gate' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/test_daemon/test_daemon_verdict_line_emission_spec.spl:68:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'names the cause so a sweep can route the file to the right owner' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
