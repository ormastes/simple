# perf_primitives_spec

> Lane L observability Phase 1 — rt_profiler_*/rt_perf_* real implementations.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# perf_primitives_spec

Lane L observability Phase 1 — rt_profiler_*/rt_perf_* real implementations.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/perf_primitives_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Lane L observability Phase 1 — rt_profiler_*/rt_perf_* real implementations.

These ten externs were shared no-op stubs in the interpreter
(src/compiler_rust/compiler/src/interpreter_extern/mod.rs `rt_perf_stub`,
time.rs no-op rt_profiler_*). They are now real: Instant-backed monotonic
clock, rdtsc on x86_64, and a process-global region-stats table shared by
the rt_profiler_* (name-keyed) and rt_perf_region_* (id-keyed) probes,
dumped via rt_perf_dump_sdn().

Gate: profile a known workload, assert per-region count/min/max/avg
populated in the dump.

## Scenarios

### perf clock primitives

#### rt_perf_clock_ns is monotonic non-decreasing

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- rt_perf_clock_ns is monotonic non-decreasing
   - Expected: t2 >= t1 is true
   - Expected: t1 >= 0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rt_perf_clock_ns is monotonic non-decreasing")
val t1 = rt_perf_clock_ns()
var spin = 0
var i = 0
while i < 1000:
    spin = spin + i
    i = i + 1
val t2 = rt_perf_clock_ns()
expect(t2 >= t1).to_equal(true)
expect(t1 >= 0).to_equal(true)
```

</details>

#### rt_perf_rdtsc returns a positive cycle count

- rt_perf_rdtsc returns a positive cycle count
   - Expected: c > 0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rt_perf_rdtsc returns a positive cycle count")
val c = rt_perf_rdtsc()
expect(c > 0).to_equal(true)
```

</details>

#### rt_perf_cycles_to_ns converts at the given frequency

- rt_perf_cycles_to_ns converts at the given frequency
   - Expected: rt_perf_cycles_to_ns(3000, 3000) equals `1000`
   - Expected: rt_perf_cycles_to_ns(1, 1000) equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rt_perf_cycles_to_ns converts at the given frequency")
# 3000 cycles at 3000 MHz = 1000 ns
expect(rt_perf_cycles_to_ns(3000, 3000)).to_equal(1000)
# 1 cycle at 1000 MHz (1 GHz) = 1 ns
expect(rt_perf_cycles_to_ns(1, 1000)).to_equal(1)
```

</details>

### perf enable/clear control

#### rt_perf_enable flips rt_perf_enabled

- rt_perf_enable flips rt_perf_enabled
   - Expected: rt_perf_enabled() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rt_perf_enable flips rt_perf_enabled")
rt_perf_enable()
expect(rt_perf_enabled()).to_equal(true)
```

</details>

### profiler workload gate — per-region stats populated

#### profiles a known workload and populates count/min/max/avg

- profiles a known workload and populates count/min/max/avg
   - Expected: rt_profiler_is_active() is true
   - Expected: dump contains `workload_fn`
   - Expected: dump contains `count: 10`
   - Expected: dump contains `total_ns:`
   - Expected: dump contains `avg_ns:`
   - Expected: dump contains `min_ns:`
   - Expected: dump contains `max_ns:`
   - Expected: dump does not contain `total_ns: 0\n`


<details>
<summary>Executable SSpec</summary>

Runnable source: 27 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("profiles a known workload and populates count/min/max/avg")
rt_perf_clear()
expect(rt_profiler_is_active()).to_equal(true)

# Known workload: 10 profiled calls of a spin loop.
var run = 0
while run < 10:
    rt_profiler_record_call("workload_fn", "perf_primitives_spec.spl", 1)
    var acc = 0
    var i = 0
    while i < 500:
        acc = acc + i
        i = i + 1
    rt_profiler_record_return("workload_fn", "perf_primitives_spec.spl", 2)
    run = run + 1

val dump = rt_perf_dump_sdn()
expect(dump.contains("workload_fn")).to_equal(true)
expect(dump.contains("count: 10")).to_equal(true)
expect(dump.contains("total_ns:")).to_equal(true)
expect(dump.contains("avg_ns:")).to_equal(true)
expect(dump.contains("min_ns:")).to_equal(true)
expect(dump.contains("max_ns:")).to_equal(true)
# Real timing: min/max must not be the "never recorded" zero-pair
# AND total must be nonzero for 10 spin loops.
expect(dump.contains("total_ns: 0\n")).to_equal(false)
```

</details>

#### rt_perf_region_enter/exit records under region:<id> when enabled

- rt_perf_region_enter/exit records under region:<id> when enabled
   - Expected: dump contains `region:7`
   - Expected: dump contains `count: 1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rt_perf_region_enter/exit records under region:<id> when enabled")
rt_perf_clear()
rt_perf_enable()
rt_perf_region_enter(7, "perf_primitives_spec.spl", 10)
var acc = 0
var i = 0
while i < 100:
    acc = acc + i
    i = i + 1
rt_perf_region_exit(7, "perf_primitives_spec.spl", 12)

val dump = rt_perf_dump_sdn()
expect(dump.contains("region:7")).to_equal(true)
expect(dump.contains("count: 1")).to_equal(true)
```

</details>

#### rt_perf_clear empties the stats table

- rt_perf_clear empties the stats table
   - Expected: dump contains `[]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rt_perf_clear empties the stats table")
rt_perf_clear()
val dump = rt_perf_dump_sdn()
expect(dump.contains("[]")).to_equal(true)
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

- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `129b7775af7edf74c66c18d5ef2c0d241f8ddbfe0f95b50c2d54fbdcfae4d32e`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `129b7775af7edf74c66c18d5ef2c0d241f8ddbfe0f95b50c2d54fbdcfae4d32e`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `129b7775af7edf74c66c18d5ef2c0d241f8ddbfe0f95b50c2d54fbdcfae4d32e`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/01_unit/lib/perf_primitives_spec.spl
mirror: doc/06_spec/01_unit/lib/perf_primitives_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/perf_primitives_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/perf_primitives_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/perf_primitives_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/perf_primitives_spec.spl:43:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rt_perf_clock_ns is monotonic non-decreasing' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/perf_primitives_spec.spl:56:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rt_perf_rdtsc returns a positive cycle count' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/perf_primitives_spec.spl:62:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rt_perf_cycles_to_ns converts at the given frequency' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
