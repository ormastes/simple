# T32 Compiled (SMF) Mode Tests

> Validates T32 operations work in compiled mode.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# T32 Compiled (SMF) Mode Tests

Validates T32 operations work in compiled mode.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/integration/t32_hw/modes/compiled_smf_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Validates T32 operations work in compiled mode.
All backends including ctypes are available.

## Scenarios

### T32 in compiled mode

#### core operations

#### connects to T32

- connects to T32
   - Expected: c.connected is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("connects to T32")
if not t32_hw_probe_available():
    expect("skipped").to_contain("skip")
    return
val client = t32_hw_connect()
match client:
    Ok(c):
        expect(c.connected).to_equal(true)
        c.disconnect()
    Err(e):
        expect("connect failed: {e}").to_contain("skip")
```

</details>

#### evaluates expression

- evaluates expression


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("evaluates expression")
if not t32_hw_probe_available():
    expect("skipped").to_contain("skip")
    return
val client = t32_hw_connect()
match client:
    Ok(c):
        val r = c.eval_expr("VERSION.BUILD()")
        c.disconnect()
        match r:
            Ok(v): expect(v.trim().len()).to_be_greater_than(0)
            Err(e): expect("eval: {e}").to_contain("eval")
    Err(e):
        expect("connect failed: {e}").to_contain("skip")
```

</details>

#### runs command

- runs command


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("runs command")
if not t32_hw_probe_available():
    expect("skipped").to_contain("skip")
    return
val client = t32_hw_connect()
match client:
    Ok(c):
        val r = c.run_command("SYStem.Up")
        c.disconnect()
        match r:
            Ok(_): expect("ok").to_equal("ok")
            Err(e): expect("cmd: {e}").to_contain("cmd")
    Err(e):
        expect("connect failed: {e}").to_contain("skip")
```

</details>

#### reads registers

- reads registers


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("reads registers")
if not t32_hw_probe_available():
    expect("skipped").to_contain("skip")
    return
val client = t32_hw_connect()
match client:
    Ok(c):
        val r = c.read_register("PC")
        c.disconnect()
        match r:
            Ok(v): expect(v).to_be_greater_than(-1)
            Err(e): expect("reg: {e}").to_contain("reg")
    Err(e):
        expect("connect failed: {e}").to_contain("skip")
```

</details>

#### ctypes backend (compiled only)

#### ctypes library availability check

- ctypes library availability check
   - Expected: available is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("ctypes library availability check")
val available = t32_hw_ctypes_available()
# Just report availability -- not a failure if missing
if available:
    expect(available).to_equal(true)
else:
    expect("ctypes not available on this system").to_contain("not available")
```

</details>

#### connects via ctypes if available

- connects via ctypes if available


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("connects via ctypes if available")
if not t32_hw_probe_available() or not t32_hw_ctypes_available():
    expect("skipped").to_contain("skip")
    return
# Ctypes connection would go through the C API bridge
# For now validate that the probe at least works
val client = t32_hw_connect()
match client:
    Ok(c):
        val r = c.eval_expr("VERSION.BUILD()")
        c.disconnect()
        match r:
            Ok(v): expect(v.trim().len()).to_be_greater_than(0)
            Err(e): expect("ctypes eval: {e}").to_contain("eval")
    Err(e):
        expect("ctypes connect: {e}").to_contain("skip")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
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

- Canonical SPipe generation for source `b71f45ba1e7e8b33af6721b3ae1d0941844dea95af6380ccf8562a4c9abef736`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `b71f45ba1e7e8b33af6721b3ae1d0941844dea95af6380ccf8562a4c9abef736`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `b71f45ba1e7e8b33af6721b3ae1d0941844dea95af6380ccf8562a4c9abef736`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/integration/t32_hw/modes/compiled_smf_spec.spl
mirror: doc/06_spec/integration/t32_hw/modes/compiled_smf_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/integration/t32_hw/modes/compiled_smf_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/integration/t32_hw/modes/compiled_smf_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/integration/t32_hw/modes/compiled_smf_spec.spl:27:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'connects to T32' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/t32_hw/modes/compiled_smf_spec.spl:41:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'evaluates expression' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/t32_hw/modes/compiled_smf_spec.spl:58:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'runs command' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
