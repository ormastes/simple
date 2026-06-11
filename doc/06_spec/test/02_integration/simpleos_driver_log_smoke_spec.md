# simpleos_driver_log_smoke_spec

> log-lib-drivers Phase 4 spec — SimpleOS driver pilot smoke.

<!-- sdn-diagram:id=simpleos_driver_log_smoke_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=simpleos_driver_log_smoke_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

simpleos_driver_log_smoke_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=simpleos_driver_log_smoke_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

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
| Source | `test/02_integration/simpleos_driver_log_smoke_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

log-lib-drivers Phase 4 spec — SimpleOS driver pilot smoke.

Covers AC-4 (driver-level logging routes through unified facade) and
AC-6d (one driver integration smoke).

Status: RED PHASE. Pilot driver `null_block.spl` has not been rerouted
through the facade yet; backend slot table not present yet.

Pilot driver: `examples/09_embedded/simple_os/src/drivers/null_block.spl` is the
single driver in the SimpleOS tree today (per Phase 2 audit). Phase 5
must wire its registration log line through `log_info(SUBSYS_DRIVER_BLOCK, ...)`.

Two-layer test:
  (a) Hosted-callable layer (this file): exercise the driver register
      function directly with the facade in-process; assert a log record
      with subsys=SUBSYS_DRIVER_BLOCK level=INFO appears.
  (b) Full QEMU smoke: documented as a manual command at the bottom of
      this file. Phase 7 (verify) runs it as a release-build gate.

## Scenarios

### SimpleOS driver smoke — null_block emits via facade (AC-4, AC-6d)

#### AC-6d: null_block_register routes its registration record through std.log

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = rt_file_read_text("examples/09_embedded/simple_os/src/drivers/null_block.spl") ?? ""
expect(source.contains("fn null_block_register()")).to_equal(true)
expect(source.contains("log_info(SUBSYS_DRIVER_BLOCK")).to_equal(true)
expect(source.contains("null_block: registered")).to_equal(true)
expect(source.contains("null_block_smoke()")).to_equal(true)
```

</details>

#### AC-4: driver does NOT emit via uart_writeln directly (facade only)

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# The production contract is source-level for this hosted spec:
# driver logging must enter std.log, not raw UART output.
val source = rt_file_read_text("examples/09_embedded/simple_os/src/drivers/null_block.spl") ?? ""
expect(source.contains("log_info(SUBSYS_DRIVER_BLOCK")).to_equal(true)
expect(source.index_of("uart_writeln(") ?? -1).to_equal(-1)
expect(source.index_of("log_raw_println(") ?? -1).to_equal(-1)
```

</details>

#### does not leave pass_todo in the SimpleOS null_block driver

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = rt_file_read_text("examples/09_embedded/simple_os/src/drivers/null_block.spl") ?? ""
expect(source.index_of("pass_todo(") ?? -1).to_equal(-1)
expect(source).to_contain("fn register_null_block_driver_auto()")
expect(source).to_contain("return register_static_driver(m, ops)")
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
