# product_dynload_startup_spec

> Product dynload startup cutover specification.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# product_dynload_startup_spec

Product dynload startup cutover specification.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/startup/product_dynload_startup_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Product dynload startup cutover specification.

Proves checked config admission is fail-closed, raw-APK compatibility remains
a separate deferred owner, checked libraries close in reverse order, and
observational counters do not invent latency or max-RSS admission.

## Scenarios

### product dynload startup config cutover

#### fails malformed config without touching deferred raw APK compatibility

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- fails malformed config without touching deferred raw APK compatibility
- Verify: malformed checked config has no raw APK interaction
   - Expected: owner.config_ok is false
   - Expected: owner.exit_code equals `1`
   - Expected: owner.metrics.raw_pack_file_reads equals `-1`
   - Expected: owner.metrics.config_file_reads equals `1`
   - Expected: owner.close() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("fails malformed config without touching deferred raw APK compatibility")
step("Verify: malformed checked config has no raw APK interaction")
val owner = product_dynload_startup_from_values(
    [], "", "", "spec-config-fail", startup_manifest(),
    "dynload:\n  lib_a: \"presence=maybe\"\n", "", 17, 1)
expect(owner.config_ok).to_equal(false)
expect(owner.exit_code).to_equal(1)
expect(owner.metrics.raw_pack_file_reads).to_equal(-1)
expect(owner.metrics.raw_apk_counter_state).to_equal(
    "not-owned-deferred")
expect(owner.metrics.raw_apk_compat_path).to_equal(
    "app.cli.startup_aspect_packs")
expect(owner.metrics.config_file_reads).to_equal(1)
expect(owner.close()).to_equal(true)
```

</details>

#### owns checked dynSMF lifecycle and closes it idempotently

- owns checked dynSMF lifecycle and closes it idempotently
- Verify: checked startup has exactly one lifecycle owner
   - Expected: owner.config_ok is true
   - Expected: owner.exit_code equals `0`
   - Expected: owner.closed is false
   - Expected: owner.close() is true
   - Expected: owner.closed is true
   - Expected: owner.close() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("owns checked dynSMF lifecycle and closes it idempotently")
step("Verify: checked startup has exactly one lifecycle owner")
val owner = product_dynload_startup_from_values(
    [], "", "", "spec-close", startup_manifest(), "", "", 19, 0)
expect(owner.config_ok).to_equal(true)
expect(owner.exit_code).to_equal(0)
expect(owner.closed).to_equal(false)
expect(owner.close()).to_equal(true)
expect(owner.closed).to_equal(true)
expect(owner.close()).to_equal(true)
```

</details>

#### fails valid config when checked artifact admission fails

- fails valid config when checked artifact admission fails
- Verify: checked load failure cannot return startup success
   - Expected: owner.config_ok is true
   - Expected: owner.exit_code equals `1`
   - Expected: owner.close() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("fails valid config when checked artifact admission fails")
step("Verify: checked load failure cannot return startup success")
val owner = product_dynload_startup_from_values(
    [], "", "", "spec-artifact-fail", startup_manifest(),
    "dynload:\n  lib_a: \"presence=on,placement=dynamic,activation=startup\"\n",
    "", 23, 1)
expect(owner.config_ok).to_equal(true)
expect(owner.exit_code).to_equal(1)
expect(owner.error).to_contain("dynload startup rejected")
expect(owner.close()).to_equal(true)
```

</details>

#### closes checked handles in reverse load order

- closes checked handles in reverse load order
- Verify: one-pass close walks last-loaded first
   - Expected: closed.evidence.len() equals `2`
   - Expected: closed.evidence[0].library_id equals `second`
   - Expected: closed.evidence[1].library_id equals `first`
   - Expected: closed.evidence[0].status equals `unloaded`
   - Expected: closed.evidence[1].status equals `unloaded`
   - Expected: closed.loaded[0].status equals `unloaded`
   - Expected: closed.loaded[1].status equals `unloaded`
   - Expected: closed.generation equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("closes checked handles in reverse load order")
step("Verify: one-pass close walks last-loaded first")
val session = DynSmfSession(
    session_id: "spec-reverse-close",
    generation: 2,
    next_handle: 3,
    policy: dynsmf_policy_default(),
    loaded: [
        DynSmfLoadedLibrary(id: "first", handle: 101, generation: 1,
            status: "loaded", symbol_registry: ""),
        DynSmfLoadedLibrary(id: "second", handle: 102, generation: 2,
            status: "loaded", symbol_registry: "")
    ],
    evidence: [])
val closed = dynsmf_session_close(session)
expect(closed.evidence.len()).to_equal(2)
expect(closed.evidence[0].library_id).to_equal("second")
expect(closed.evidence[1].library_id).to_equal("first")
expect(closed.evidence[0].status).to_equal("unloaded")
expect(closed.evidence[1].status).to_equal("unloaded")
expect(closed.loaded[0].status).to_equal("unloaded")
expect(closed.loaded[1].status).to_equal("unloaded")
expect(closed.generation).to_equal(4)
```

</details>

#### reports latency targets while leaving RSS to outer-harness evidence

- reports latency targets while leaving RSS to outer-harness evidence
- Verify: counters distinguish targets from measured evidence
   - Expected: owner.metrics.elapsed_us equals `29`
   - Expected: owner.metrics.latency_target_us equals `0`
   - Expected: owner.metrics.latency_target_configured is false
   - Expected: owner.metrics.measured_max_rss_kib equals `0`
   - Expected: owner.metrics.rss_target_configured is false
   - Expected: owner.metrics.full_tree_scans equals `0`
   - Expected: owner.metrics.child_processes equals `0`
   - Expected: owner.close() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("reports latency targets while leaving RSS to outer-harness evidence")
step("Verify: counters distinguish targets from measured evidence")
val owner = product_dynload_startup_from_values(
    [], "", "", "spec-metrics", startup_manifest(), "", "", 29, 0)
expect(owner.metrics.elapsed_us).to_equal(29)
expect(owner.metrics.latency_target_us).to_equal(0)
expect(owner.metrics.latency_target_configured).to_equal(false)
expect(owner.metrics.latency_target_source).to_equal(
    "outer-harness-required")
expect(owner.metrics.measured_max_rss_kib).to_equal(0)
expect(owner.metrics.rss_target_configured).to_equal(false)
expect(owner.metrics.rss_evidence_source).to_equal(
    "outer-harness-required")
expect(owner.metrics.full_tree_scans).to_equal(0)
expect(owner.metrics.child_processes).to_equal(0)
val line = product_dynload_startup_metrics_line(owner.metrics)
expect(line).to_contain("elapsed_us=29")
expect(line).to_contain("rss_evidence_source=outer-harness-required")
expect(line).to_contain("raw_apk_counter_state=not-owned-deferred")
expect(owner.close()).to_equal(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
- `REQ-APP-STARTUP-001`
- `REQ-APKS-01`
- `REQ-SSPEC-APP`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `f99b2c1b617e2659a9d29c00059c1fdbb6a4cc7f3e7e072f51c39d232b4e04d7`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `f99b2c1b617e2659a9d29c00059c1fdbb6a4cc7f3e7e072f51c39d232b4e04d7`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `f99b2c1b617e2659a9d29c00059c1fdbb6a4cc7f3e7e072f51c39d232b4e04d7`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **80/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/01_unit/app/startup/product_dynload_startup_spec.spl
mirror: doc/06_spec/01_unit/app/startup/product_dynload_startup_spec.md (current)
findings: 7 blockers: 1
  narrative=100 structure=100 oracle=70
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=80; blocker cap makes effective=49
doc/06_spec/01_unit/app/startup/product_dynload_startup_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/startup/product_dynload_startup_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/startup/product_dynload_startup_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 12 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/app/startup/product_dynload_startup_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 3 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/app/startup/product_dynload_startup_spec.spl:47:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'fails malformed config without touching deferred raw APK compatibility' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/startup/product_dynload_startup_spec.spl:64:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'owns checked dynSMF lifecycle and closes it idempotently' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/startup/product_dynload_startup_spec.spl:77:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'fails valid config when checked artifact admission fails' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
