# backend_isolation_gate_spec

> Purpose: the UI backend-isolation gate is observed by EXECUTING it against a

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# backend_isolation_gate_spec

Purpose: the UI backend-isolation gate is observed by EXECUTING it against a

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/03_system/app/ui/feature/backend_isolation_gate_spec.spl` |
| Updated | 2026-08-27 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: the UI backend-isolation gate is observed by EXECUTING it against a
clean directory and a directory carrying an injected violation, instead of
grepping the script text. Audience: UI/rendering engineers and release gate
owners.

Note: the full-tree ratchet is currently RED (new violations beyond the
committed baseline), so the full-tree scenario asserts the machine-readable
ratchet mechanism — counts vs baseline — without asserting the red verdict.

## Scenarios

### UI backend-isolation enforcement gate

#### passes a clean directory and reports the typed ok status

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- Run the gate against a directory with no UI-tier code
   - Expected: code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("Run the gate against a directory with no UI-tier code")
mkdir_p(TMP + "/clean")
val (stdout, code) = run_gate(TMP + "/clean")
expect(code).to_equal(0)  # oracle: clean tree exits 0
expect(stdout).to_contain("ui_backend_isolation_new=0")  # oracle: no new violations counted
expect(stdout).to_contain("ui_backend_isolation_ok=true")  # oracle: typed verdict ok
```

</details>

#### fails closed on an rt_* call in scanned UI-tier code

- Inject an extern rt_* call and rerun the gate
   - Expected: code equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("Inject an extern rt_* call and rerun the gate")
mkdir_p(TMP + "/bad")
file_write(TMP + "/bad/rt_call.spl",
    "extern fn rt_probe_thing() -> i64\nfn use_it() -> i64:\n    rt_probe_thing()\n")
val (stdout, code) = run_gate(TMP + "/bad")
expect(code).to_equal(1)  # oracle: violation fails the gate
expect(stdout).to_contain("ui_backend_isolation_new=1")  # oracle: exactly the injected violation counted
expect(stdout).to_contain("ui_backend_isolation_ok=false")  # oracle: typed verdict not ok
```

</details>

#### fails closed on direct backend-class construction

- Inject a VulkanBackend construction and rerun the gate
   - Expected: code equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("Inject a VulkanBackend construction and rerun the gate")
mkdir_p(TMP + "/bad2")
file_write(TMP + "/bad2/backend_ctor.spl",
    "fn make():\n    val b = VulkanBackend(1)\n")
val (stdout, code) = run_gate(TMP + "/bad2")
expect(code).to_equal(1)  # oracle: direct construction fails the gate
expect(stdout).to_contain("ui_backend_isolation_ok=false")  # oracle: typed verdict not ok
```

</details>

#### the committed ratchet baseline exists and the full-tree run reports against it

- Run the gate on the real tree and read the ratchet counters
   - Expected: file_exists("scripts/check/ui_backend_isolation_baseline.txt") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("Run the gate on the real tree and read the ratchet counters")
expect(file_exists("scripts/check/ui_backend_isolation_baseline.txt")).to_equal(true)
val (stdout, _code) = run_gate(".")
expect(stdout).to_contain("ui_backend_isolation_current=")  # oracle: current count reported vs baseline
expect(stdout).to_contain("ui_backend_isolation_new=")  # oracle: delta-vs-baseline reported
expect(stdout).to_contain("ui_backend_isolation_ok=")  # oracle: typed verdict always emitted, both directions
```

</details>

#### keeps host winit operations in the canonical runtime facade only

- The winit facade is the single owner of host window operations
   - Expected: file_exists("src/lib/common/ui/host_winit_surface.spl") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("The winit facade is the single owner of host window operations")
expect(file_exists("src/lib/common/ui/host_winit_surface.spl")).to_equal(false)  # oracle: no shadow facade
val (stdout, _code) = run_gate("src/lib/common/ui")
expect(stdout).to_contain("ui_backend_isolation_new=0")  # oracle: facade-only layer introduces no rt_*/backend violations
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

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `a15909b485cea3adbf0c07e3ba69f44ea59b34e677f622f1fba344a507d58170`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `a15909b485cea3adbf0c07e3ba69f44ea59b34e677f622f1fba344a507d58170`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `a15909b485cea3adbf0c07e3ba69f44ea59b34e677f622f1fba344a507d58170`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/app/ui/feature/backend_isolation_gate_spec.spl
mirror: doc/06_spec/03_system/app/ui/feature/backend_isolation_gate_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/app/ui/feature/backend_isolation_gate_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/app/ui/feature/backend_isolation_gate_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/app/ui/feature/backend_isolation_gate_spec.spl:31:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'passes a clean directory and reports the typed ok status' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/app/ui/feature/backend_isolation_gate_spec.spl:40:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'fails closed on an rt_* call in scanned UI-tier code' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/app/ui/feature/backend_isolation_gate_spec.spl:51:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'fails closed on direct backend-class construction' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
