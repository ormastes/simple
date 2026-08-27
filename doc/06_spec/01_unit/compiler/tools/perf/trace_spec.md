# trace_spec

> Lane L observability Phase 1 — Chrome Trace Event Format span API.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# trace_spec

Lane L observability Phase 1 — Chrome Trace Event Format span API.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/tools/perf/trace_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Lane L observability Phase 1 — Chrome Trace Event Format span API.

perf.trace adds trace_begin/trace_end (B/E span events), a generic
trace_ingest_span() complete-span (X) ingestion hook (feeds the profiler now;
feeds a kernel scheduler-trace-ring reader once Phase 2 wires it), and
trace_to_json() emitting the Chrome Trace Event JSON format.

Gate: emit a trace, validate JSON has matching B/E events.

NOTE: imports use the direct `use module.{fns}` form, NOT
`import module as alias` — under the interpreter the aliased form binds a
separate module instance per call site, so module-global state (the trace
event buffer) written through one alias call is invisible to the next
(trace_events_count() returned 0 right after trace_begin/trace_end pushed 2).
Direct-import form shares one instance and behaves correctly. Filed as an
interpreter module-aliasing state bug alongside this lane's work.

## Scenarios

### chrome trace — begin/end span events

#### emits matching B/E events for one span

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- emits matching B/E events for one span
   - Expected: trace_events_count() equals `2`
   - Expected: j contains `"ph":"B"`
   - Expected: j contains `"ph":"E"`
   - Expected: j contains `"name":"region_a"`
   - Expected: j contains `"traceEvents"`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("emits matching B/E events for one span")
trace_clear()
trace_begin("region_a", "test", 0)
trace_end("region_a", "test", 0)

expect(trace_events_count()).to_equal(2)

val j = trace_to_json()
expect(j.contains("\"ph\":\"B\"")).to_equal(true)
expect(j.contains("\"ph\":\"E\"")).to_equal(true)
expect(j.contains("\"name\":\"region_a\"")).to_equal(true)
expect(j.contains("\"traceEvents\"")).to_equal(true)
```

</details>

#### emits a complete (X) span with a duration via trace_ingest_span

- emits a complete (X) span with a duration via trace_ingest_span
   - Expected: trace_events_count() equals `1`
   - Expected: j contains `"ph":"X"`
   - Expected: j contains `"dur":4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("emits a complete (X) span with a duration via trace_ingest_span")
trace_clear()
trace_ingest_span("ingested", "sched", 1000, 5000, 2)

val j = trace_to_json()
expect(trace_events_count()).to_equal(1)
expect(j.contains("\"ph\":\"X\"")).to_equal(true)
expect(j.contains("\"dur\":4")).to_equal(true)  # (5000-1000)ns / 1000 = 4us
```

</details>

### chrome trace — fed from profiler.spl

#### trace_from_profiler feeds one X event per profiled region

- trace_from_profiler feeds one X event per profiled region
   - Expected: trace_events_count() equals `1`
   - Expected: j contains `"name":"hot_region"`
   - Expected: j contains `"ph":"X"`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("trace_from_profiler feeds one X event per profiled region")
trace_clear()
init_profiler()
var prof = get_profiler()
prof.enable()

var i = 0
while i < 50:
    val start = prof.start_region("hot_region")
    i = i + 1
    prof.end_region("hot_region", start)

trace_from_profiler(prof)

expect(trace_events_count()).to_equal(1)
val j = trace_to_json()
expect(j.contains("\"name\":\"hot_region\"")).to_equal(true)
expect(j.contains("\"ph\":\"X\"")).to_equal(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-COMPILER`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `e60c58147d391fe3ea7ad4e49715864fbe4c6ba773f7048387a682ca194a2d00`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `e60c58147d391fe3ea7ad4e49715864fbe4c6ba773f7048387a682ca194a2d00`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `e60c58147d391fe3ea7ad4e49715864fbe4c6ba773f7048387a682ca194a2d00`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/compiler/tools/perf/trace_spec.spl
mirror: doc/06_spec/01_unit/compiler/tools/perf/trace_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/tools/perf/trace_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/tools/perf/trace_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/tools/perf/trace_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 3 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/tools/perf/trace_spec.spl:36:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'emits matching B/E events for one span' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/tools/perf/trace_spec.spl:51:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'emits a complete (X) span with a duration via trace_ingest_span' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/tools/perf/trace_spec.spl:64:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'trace_from_profiler feeds one X event per profiled region' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
