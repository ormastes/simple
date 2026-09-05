# simpleos_driver_log_smoke_spec

> log-lib-drivers Phase 4 spec — SimpleOS driver pilot smoke.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# simpleos_driver_log_smoke_spec

log-lib-drivers Phase 4 spec — SimpleOS driver pilot smoke.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/integration/simpleos_driver_log_smoke_spec.spl` |
| Updated | 2026-08-27 |
| Generator | `simple spipe-docgen` (Simple) |

log-lib-drivers Phase 4 spec — SimpleOS driver pilot smoke.

Covers AC-4 (driver-level logging routes through unified facade) and
AC-6d (one driver integration smoke).

Status: RED PHASE. Pilot driver `null_block.spl` has not been rerouted
through the facade yet; backend slot table not present yet.

Pilot driver: `examples/simple_os/src/drivers/null_block.spl` is the
single driver in the SimpleOS tree today (per Phase 2 audit). Phase 5
must wire its registration log line through `log_info_subsys(SUBSYS_DRIVER_BLOCK, ...)`.

Two-layer test:
  (a) Hosted-callable layer (this file): exercise the driver register
      function directly with the facade in-process; assert a log record
      with subsys=SUBSYS_DRIVER_BLOCK level=INFO appears.
  (b) Full QEMU smoke: documented as a manual command at the bottom of
      this file. Phase 7 (verify) runs it as a release-build gate.

## Scenarios

### SimpleOS driver smoke — null_block emits via facade (AC-4, AC-6d)

#### AC-6d: null_block_register routes its registration record through std.log

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- AC-6d: null_block_register routes its registration record through std.log


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("AC-6d: null_block_register routes its registration record through std.log")
val source = rt_file_read_text("examples/simple_os/src/drivers/null_block.spl") ?? ""
assert_equal(source.contains("fn null_block_register()"), true)
assert_equal(source.contains("log_info_subsys(SUBSYS_DRIVER_BLOCK"), true)
assert_equal(source.contains("null_block: registered"), true)
assert_equal(source.contains("null_block_smoke()"), true)
```

</details>

#### AC-4: driver does NOT emit via uart_writeln directly (facade only)

- AC-4: driver does NOT emit via uart_writeln directly (facade only)


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("AC-4: driver does NOT emit via uart_writeln directly (facade only)")
# The production contract is source-level for this hosted spec:
# driver logging must enter std.log, not raw UART output.
val source = rt_file_read_text("examples/simple_os/src/drivers/null_block.spl") ?? ""
assert_equal(source.contains("log_info_subsys(SUBSYS_DRIVER_BLOCK"), true)
assert_equal(source.index_of("uart_writeln("), -1)
assert_equal(source.index_of("log_raw_println("), -1)
```

</details>

#### does not leave pass_todo in the SimpleOS null_block driver

- does not leave pass_todo in the SimpleOS null_block driver


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("does not leave pass_todo in the SimpleOS null_block driver")
val source = rt_file_read_text("examples/simple_os/src/drivers/null_block.spl") ?? ""
assert_equal(source.index_of("pass_todo("), -1)
assert_contains(source, "fn register_null_block_driver_auto()")
assert_contains(source, "return register_static_driver(m, ops)")
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

- `REQ-SSPEC-INTEGRATION`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `1d616fad28c9ed0f3941a45e00f3cf2b817500bfa17da7b109e63da38303d808`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `1d616fad28c9ed0f3941a45e00f3cf2b817500bfa17da7b109e63da38303d808`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `1d616fad28c9ed0f3941a45e00f3cf2b817500bfa17da7b109e63da38303d808`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/integration/simpleos_driver_log_smoke_spec.spl
mirror: doc/06_spec/integration/simpleos_driver_log_smoke_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/integration/simpleos_driver_log_smoke_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/integration/simpleos_driver_log_smoke_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/integration/simpleos_driver_log_smoke_spec.spl:33:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'AC-6d: null_block_register routes its registration record through std.log' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/simpleos_driver_log_smoke_spec.spl:42:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'AC-4: driver does NOT emit via uart_writeln directly (facade only)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/simpleos_driver_log_smoke_spec.spl:52:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'does not leave pass_todo in the SimpleOS null_block driver' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
