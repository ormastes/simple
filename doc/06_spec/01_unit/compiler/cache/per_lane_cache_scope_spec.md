# Per-Lane Private Build Caches

> The bootstrap runs several lanes at once — phase-1 seed, phase-2 stage, phase-3

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Per-Lane Private Build Caches

The bootstrap runs several lanes at once — phase-1 seed, phase-2 stage, phase-3

## At a Glance

| Field | Value |
|-------|-------|
| Category | Infrastructure |
| Status | Implemented |
| Design | doc/05_design/compiler/incremental_build/per_lane_private_caches.md |
| Source | `test/01_unit/compiler/cache/per_lane_cache_scope_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and Audience

The bootstrap runs several lanes at once — phase-1 seed, phase-2 stage, phase-3
self-host, phase-4 full CLI, plus census and tool-build lanes. Each may drive a
DIFFERENT compiler binary over the SAME source tree. Until 2026-08-17 they all
shared one `build/bootstrap/native_cache`, so an object produced by the phase-2
compiler could be picked up by a phase-3 lane, and a fix landing mid-run could
leave a stale entry that is silently wrong.

This spec is the REPRODUCING spec for that defect: it drives the real ownership
guard over two lanes pointed at one cache directory and requires the second lane
to be REFUSED. A cache change that keeps hitting across scopes is worse than no
change, so the cross-scope refusal is asserted directly, not inferred.

## Scope and Preconditions

Runs the shell guard `scripts/check/check-cache-scope-ownership.shs` as a
subprocess over throwaway directories under `build/test-artifacts/`. It touches
no compiler and needs no build.

## Primary Workflow

A lane claims an unowned cache directory; the same lane reuses it; a second lane
asking for the same directory is refused by name; the second lane's own private
directory is granted.

## Key Concepts

| Concept | Description |
|---------|-------------|
| lane | The declared private-cache scope, `SIMPLE_CACHE_SCOPE` / `--cache-scope` |
| `.cache_scope` marker | File inside a cache dir recording the lane that owns it |
| verdict line | Last line of stdout: `PASS`/`FAIL`/`ERROR`, exit 0/1/2 |

## Scenarios

### Per-lane private build caches

#### grants a lane its own cache and lets that same lane reuse it

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- grants a lane its own cache and lets that same lane reuse it
- A phase-2 lane claims an unowned cache directory
   - Expected: first_code equals `0`
- The ownership marker records the lane that claimed it
- The same lane asks again and is granted the same directory
   - Expected: second_code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("grants a lane its own cache and lets that same lane reuse it")
step("A phase-2 lane claims an unowned cache directory")
val dir = scratch("reuse")
val (first, first_code) = run_guard(dir, "stage2")
expect(first).to_contain("PASS")
expect(first).to_contain("stage2")
expect(first_code).to_equal(0)

step("The ownership marker records the lane that claimed it")
expect(file_exists(dir + "/.cache_scope")).to_be(true)

step("The same lane asks again and is granted the same directory")
val (second, second_code) = run_guard(dir, "stage2")
expect(second).to_contain("PASS")
expect(second_code).to_equal(0)
```

</details>

#### refuses a second lane that points at the first lane's cache

- refuses a second lane that points at the first lane's cache
- A phase-2 lane owns the cache directory
   - Expected: claim_code equals `0`
- A phase-3 lane, running a different compiler, asks for the same dir
- The guard refuses and names BOTH scopes, so the miss is auditable
   - Expected: refusal_code equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("refuses a second lane that points at the first lane's cache")
step("A phase-2 lane owns the cache directory")
val dir = scratch("crossscope")
val (_claim, claim_code) = run_guard(dir, "stage2")
expect(claim_code).to_equal(0)

step("A phase-3 lane, running a different compiler, asks for the same dir")
val (refusal, refusal_code) = run_guard(dir, "stage3")

step("The guard refuses and names BOTH scopes, so the miss is auditable")
expect(refusal).to_contain("FAIL")
expect(refusal).to_contain("stage2")
expect(refusal).to_contain("stage3")
expect(refusal_code).to_equal(1)
```

</details>

#### grants the second lane its own private directory instead

- grants the second lane its own private directory instead
- The phase-3 lane uses its own private cache dir
   - Expected: code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("grants the second lane its own private directory instead")
step("The phase-3 lane uses its own private cache dir")
val dir = scratch("stage3_private")
val (out, code) = run_guard(dir, "stage3")
expect(out).to_contain("PASS")
expect(out).to_contain("stage3")
expect(code).to_equal(0)
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


## Related Documentation

- **Design:** `doc/05_design/compiler/incremental_build/per_lane_private_caches.md`


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-COMPILER`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `39c15d4b9ae4059d7c522eea192188cd6e9cf58743cc7df60de8a9d43d3e9e10`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `39c15d4b9ae4059d7c522eea192188cd6e9cf58743cc7df60de8a9d43d3e9e10`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `39c15d4b9ae4059d7c522eea192188cd6e9cf58743cc7df60de8a9d43d3e9e10`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/compiler/cache/per_lane_cache_scope_spec.spl
mirror: doc/06_spec/01_unit/compiler/cache/per_lane_cache_scope_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/cache/per_lane_cache_scope_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/cache/per_lane_cache_scope_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/cache/per_lane_cache_scope_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 5 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/cache/per_lane_cache_scope_spec.spl:67:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'grants a lane its own cache and lets that same lane reuse it' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/cache/per_lane_cache_scope_spec.spl:85:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'refuses a second lane that points at the first lane's cache' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/cache/per_lane_cache_scope_spec.spl:102:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'grants the second lane its own private directory instead' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
