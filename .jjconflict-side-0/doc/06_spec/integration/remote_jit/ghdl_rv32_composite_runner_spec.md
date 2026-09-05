# GHDL RV32 Baremetal Composite Runner

> Verifies JIT pipeline end-to-end on GHDL RV32 simulation (no hardware required).

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# GHDL RV32 Baremetal Composite Runner

Verifies JIT pipeline end-to-end on GHDL RV32 simulation (no hardware required).

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/integration/remote_jit/ghdl_rv32_composite_runner_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Verifies JIT pipeline end-to-end on GHDL RV32 simulation (no hardware required).

## Scenarios

### GHDL RV32 Baremetal Workload

#### reports capability status for GHDL semihost lane

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- reports capability status for GHDL semihost lane
   - Expected: report.lane_id equals `ghdl_rv32_semihost`
   - Expected: report.is_acceptable() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("reports capability status for GHDL semihost lane")
val report = probe_ghdl()
expect(report.lane_id).to_equal("ghdl_rv32_semihost")
expect(report.is_acceptable()).to_equal(true)
```

</details>

#### reports capability status for GHDL mailbox lane

- reports capability status for GHDL mailbox lane
   - Expected: report.lane_id equals `ghdl_rv32_mailbox`
   - Expected: report.is_acceptable() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("reports capability status for GHDL mailbox lane")
val report = probe_ghdl_mailbox()
expect(report.lane_id).to_equal("ghdl_rv32_mailbox")
expect(report.is_acceptable()).to_equal(true)
```

</details>

#### refuses manager creation before connect

- refuses manager creation before connect
   - Expected: mgr.is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("refuses manager creation before connect")
val adapter = GhdlRv32Adapter.new()
val mgr = adapter.create_manager()
expect(mgr.is_err()).to_equal(true)
expect(mgr.err().unwrap()).to_contain("not connected")
```

</details>

#### mailbox adapter rejects execute without elf

- mailbox adapter rejects execute without elf
   - Expected: result.is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("mailbox adapter rejects execute without elf")
var adapter = GhdlRv32MailboxAdapter.new()
val result = adapter.execute()
expect(result.is_err()).to_equal(true)
expect(result.err().unwrap()).to_contain("no ELF path")
```

</details>

<details>
<summary>Advanced: reports compile failure for invalid source</summary>

#### reports compile failure for invalid source _(slow)_

- reports compile failure for invalid source
   - Expected: compiled.is_ok() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("reports compile failure for invalid source")
# NOTE: CompilerBridge.compile() is currently a stub that always returns Ok.
# This test documents the intended contract: invalid source should fail.
# When the real compiler pipeline lands, change the assertion to is_err().
val source = "this is not valid Simple code !!!"
val limits = MemoryMap.ghdl_rv32()
val compiled = CompilerBridge.compile(source, Architecture.RiscV32, limits.code_start)
expect(compiled.is_ok()).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: runs return-zero on GHDL RV32</summary>

#### runs return-zero on GHDL RV32 _(slow)_

- runs return-zero on GHDL RV32
   - Expected: result.ok.unwrap().return_value equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 29 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("runs return-zero on GHDL RV32")
if not ghdl_tools_ready():
    print "[skip] {ghdl_skip_reason()}"
    return
var adapter = GhdlRv32Adapter.new()
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
val limits = MemoryMap.ghdl_rv32()
val compiled = CompilerBridge.compile(source, Architecture.RiscV32, limits.code_start)
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
<summary>Advanced: runs return-42 on GHDL RV32</summary>

#### runs return-42 on GHDL RV32 _(slow)_

- runs return-42 on GHDL RV32
   - Expected: result.ok.unwrap().return_value equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 29 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("runs return-42 on GHDL RV32")
if not ghdl_tools_ready():
    print "[skip] {ghdl_skip_reason()}"
    return
var adapter = GhdlRv32Adapter.new()
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
val limits = MemoryMap.ghdl_rv32()
val compiled = CompilerBridge.compile(source, Architecture.RiscV32, limits.code_start)
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
| Total scenarios | 7 |
| Active scenarios | 7 |
| Slow scenarios | 3 |
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

- Canonical SPipe generation for source `daa159a262a843a23f20e91d1545b431457ba1e96287178acf31315109978673`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `daa159a262a843a23f20e91d1545b431457ba1e96287178acf31315109978673`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `daa159a262a843a23f20e91d1545b431457ba1e96287178acf31315109978673`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/integration/remote_jit/ghdl_rv32_composite_runner_spec.spl
mirror: doc/06_spec/integration/remote_jit/ghdl_rv32_composite_runner_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/integration/remote_jit/ghdl_rv32_composite_runner_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/integration/remote_jit/ghdl_rv32_composite_runner_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/integration/remote_jit/ghdl_rv32_composite_runner_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/integration/remote_jit/ghdl_rv32_composite_runner_spec.spl:30:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reports capability status for GHDL semihost lane' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/remote_jit/ghdl_rv32_composite_runner_spec.spl:37:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reports capability status for GHDL mailbox lane' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/remote_jit/ghdl_rv32_composite_runner_spec.spl:44:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'refuses manager creation before connect' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
