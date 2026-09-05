# QEMU ARM Baremetal Composite Runner

> Verifies JIT pipeline end-to-end on QEMU ARM via unified adapter.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# QEMU ARM Baremetal Composite Runner

Verifies JIT pipeline end-to-end on QEMU ARM via unified adapter.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/integration/remote_jit/qemu_arm_composite_runner_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Verifies JIT pipeline end-to-end on QEMU ARM via unified adapter.

## Scenarios

### QEMU ARM Baremetal Workload

<details>
<summary>Advanced: runs return-zero on QEMU ARM</summary>

#### runs return-zero on QEMU ARM _(slow)_

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- runs return-zero on QEMU ARM
   - Expected: result.ok.unwrap().return_value equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 29 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("runs return-zero on QEMU ARM")
if not qemu_arm_available():
    print "[skip] QEMU ARM tools not available"
    return
var adapter = QemuArmAdapter.new()
val conn = adapter.connect()
if conn.is_err():
    print "[skip] connect failed: {conn.err().unwrap()}"
    return
val mgr = adapter.create_manager()
if mgr.is_err():
    adapter.disconnect()
    print "[skip] manager failed"
    return
val source = "fn main() -> i64:\n    0\n"
val limits = MemoryMap.qemu_arm()
val compiled = CompilerBridge.compile(source, Architecture.Arm32, limits.code_start)
if compiled.is_err():
    adapter.disconnect()
    print "[skip] compile failed"
    return
var manager = mgr.ok.unwrap()
val result = manager.execute_bytes("workload_zero", compiled.ok.unwrap(), [])
adapter.disconnect()
if result.is_err():
    print "[skip] exec failed: {result.err().unwrap()}"
else:
    expect(result.ok.unwrap().return_value).to_equal(0)
```

</details>


</details>

<details>
<summary>Advanced: runs return-42 on QEMU ARM</summary>

#### runs return-42 on QEMU ARM _(slow)_

- runs return-42 on QEMU ARM
   - Expected: result.ok.unwrap().return_value equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 29 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("runs return-42 on QEMU ARM")
if not qemu_arm_available():
    print "[skip] QEMU ARM tools not available"
    return
var adapter = QemuArmAdapter.new()
val conn = adapter.connect()
if conn.is_err():
    print "[skip] connect failed: {conn.err().unwrap()}"
    return
val mgr = adapter.create_manager()
if mgr.is_err():
    adapter.disconnect()
    print "[skip] manager failed"
    return
val source = "fn main() -> i64:\n    42\n"
val limits = MemoryMap.qemu_arm()
val compiled = CompilerBridge.compile(source, Architecture.Arm32, limits.code_start)
if compiled.is_err():
    adapter.disconnect()
    print "[skip] compile failed"
    return
var manager = mgr.ok.unwrap()
val result = manager.execute_bytes("workload_42", compiled.ok.unwrap(), [])
adapter.disconnect()
if result.is_err():
    print "[skip] exec failed: {result.err().unwrap()}"
else:
    expect(result.ok.unwrap().return_value).to_equal(42)
```

</details>


</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 2 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-INTEGRATION`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `f727a41b3f1f49009203464920f2d3d5a91e2d9085d3a1e972ace8d2e6382ec7`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `f727a41b3f1f49009203464920f2d3d5a91e2d9085d3a1e972ace8d2e6382ec7`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `f727a41b3f1f49009203464920f2d3d5a91e2d9085d3a1e972ace8d2e6382ec7`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/integration/remote_jit/qemu_arm_composite_runner_spec.spl
mirror: doc/06_spec/integration/remote_jit/qemu_arm_composite_runner_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/integration/remote_jit/qemu_arm_composite_runner_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/integration/remote_jit/qemu_arm_composite_runner_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/integration/remote_jit/qemu_arm_composite_runner_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/integration/remote_jit/qemu_arm_composite_runner_spec.spl:26:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'runs return-zero on QEMU ARM' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/remote_jit/qemu_arm_composite_runner_spec.spl:57:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'runs return-42 on QEMU ARM' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
