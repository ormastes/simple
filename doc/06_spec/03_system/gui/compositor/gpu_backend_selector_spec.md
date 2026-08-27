# gpu_backend_selector_spec

> Feature: GPU backend selector (TODO #29)

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# gpu_backend_selector_spec

Feature: GPU backend selector (TODO #29)

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/gui/compositor/gpu_backend_selector_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Feature: GPU backend selector (TODO #29)
Category: compositor / display
Status: RED

## Scenarios

### select_backend with has_gpu=true

#### routes to the GPU backend contract

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- routes to the GPU backend contract
   - Expected: code equals `0`
   - Expected: stdout contains `Passed: 1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("routes to the GPU backend contract")
val (stdout, _stderr, code) = run_selector_probe(true)
expect(code).to_equal(0)
expect(stdout.contains("Passed: 1")).to_equal(true)
```

</details>

### select_backend with has_gpu=false

#### routes to the framebuffer fallback contract

- routes to the framebuffer fallback contract
   - Expected: code equals `0`
   - Expected: stdout contains `Passed: 1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("routes to the framebuffer fallback contract")
val (stdout, _stderr, code) = run_selector_probe(false)
expect(code).to_equal(0)
expect(stdout.contains("Passed: 1")).to_equal(true)
```

</details>

### CompositorBackend trait parity

#### supports the shared backend surface for both capability branches

- supports the shared backend surface for both capability branches
   - Expected: gpu_code equals `0`
   - Expected: fb_code equals `0`
   - Expected: gpu_stdout contains `Passed: 1`
   - Expected: fb_stdout contains `Passed: 1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("supports the shared backend surface for both capability branches")
val (gpu_stdout, _gpu_stderr, gpu_code) = run_selector_probe(true)
val (fb_stdout, _fb_stderr, fb_code) = run_selector_probe(false)
expect(gpu_code).to_equal(0)
expect(fb_code).to_equal(0)
expect(gpu_stdout.contains("Passed: 1")).to_equal(true)
expect(fb_stdout.contains("Passed: 1")).to_equal(true)
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

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `500926f21f4b78553fd7264c4bcc814428062dd1a24bc125416316cb7c861933`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `500926f21f4b78553fd7264c4bcc814428062dd1a24bc125416316cb7c861933`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `500926f21f4b78553fd7264c4bcc814428062dd1a24bc125416316cb7c861933`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/03_system/gui/compositor/gpu_backend_selector_spec.spl
mirror: doc/06_spec/03_system/gui/compositor/gpu_backend_selector_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/gui/compositor/gpu_backend_selector_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/gui/compositor/gpu_backend_selector_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/gui/compositor/gpu_backend_selector_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 4 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/gui/compositor/gpu_backend_selector_spec.spl:55:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'routes to the GPU backend contract' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/gui/compositor/gpu_backend_selector_spec.spl:67:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'routes to the framebuffer fallback contract' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/gui/compositor/gpu_backend_selector_spec.spl:79:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'supports the shared backend surface for both capability branches' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
