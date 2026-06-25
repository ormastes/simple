# GHDL RV32 Baremetal Composite Runner

> Verifies JIT pipeline end-to-end on GHDL RV32 simulation (no hardware required).

<!-- sdn-diagram:id=ghdl_rv32_composite_runner_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=ghdl_rv32_composite_runner_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

ghdl_rv32_composite_runner_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=ghdl_rv32_composite_runner_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

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
| Source | `test/02_integration/remote_jit/ghdl_rv32_composite_runner_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Verifies JIT pipeline end-to-end on GHDL RV32 simulation (no hardware required).

## Scenarios

### GHDL RV32 Baremetal Workload

#### reports capability status for GHDL semihost lane

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val report = probe_ghdl()
expect(report.lane_id).to_equal("ghdl_rv32_semihost")
expect(report.is_acceptable()).to_equal(true)
```

</details>

#### reports capability status for GHDL mailbox lane

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val report = probe_ghdl_mailbox()
expect(report.lane_id).to_equal("ghdl_rv32_mailbox")
expect(report.is_acceptable()).to_equal(true)
```

</details>

#### refuses manager creation before connect

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val adapter = GhdlRv32Adapter.new()
val mgr = adapter.create_manager()
expect(mgr.is_err()).to_equal(true)
expect(mgr.err().unwrap()).to_contain("not connected")
```

</details>

#### mailbox adapter rejects execute without elf

1. var adapter = GhdlRv32MailboxAdapter new
   - Expected: result.is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var adapter = GhdlRv32MailboxAdapter.new()
val result = adapter.execute()
expect(result.is_err()).to_equal(true)
expect(result.err().unwrap()).to_contain("no ELF path")
```

</details>

<details>
<summary>Advanced: reports compile failure for invalid source</summary>

#### reports compile failure for invalid source _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. print "[skip] {ghdl skip reason
2. var adapter = GhdlRv32Adapter new
3. print "[skip] connect failed: {conn err
4. adapter disconnect
5. adapter disconnect
6. var manager = mgr ok unwrap
7. adapter disconnect
8. print "[skip] exec failed: {result err
   - Expected: result.ok.unwrap().return_value equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 27 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. print "[skip] {ghdl skip reason
2. var adapter = GhdlRv32Adapter new
3. print "[skip] connect failed: {conn err
4. adapter disconnect
5. adapter disconnect
6. var manager = mgr ok unwrap
7. adapter disconnect
8. print "[skip] exec failed: {result err
   - Expected: result.ok.unwrap().return_value equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 27 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
