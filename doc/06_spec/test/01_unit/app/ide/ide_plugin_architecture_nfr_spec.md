# ide_plugin_architecture_nfr_spec

> IDE plugin architecture NFR spec.

<!-- sdn-diagram:id=ide_plugin_architecture_nfr_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=ide_plugin_architecture_nfr_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

ide_plugin_architecture_nfr_spec -> std
ide_plugin_architecture_nfr_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=ide_plugin_architecture_nfr_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# ide_plugin_architecture_nfr_spec

IDE plugin architecture NFR spec.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Requirements | doc/02_requirements/nfr/ide_plugin_architecture.md |
| Plan | doc/03_plan/sys_test/ide_office_plugin_suite.md |
| Source | `test/01_unit/app/ide/ide_plugin_architecture_nfr_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

IDE plugin architecture NFR spec.

Measures the built-in Office plugin manifest and bridge paths used by the
current IDE plugin architecture milestone.

**Architecture:** doc/04_architecture/ide_plugin_architecture.md

## Scenarios

### IDE plugin architecture NFR probes

#### loads the built-in manifest probe within the warm NFR budget

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val warmup = ide_plugin_manifest_probe()
expect(warmup.entry_count).to_equal(13)

val start = rt_time_now_unix_micros()
val probe = ide_plugin_manifest_probe()
val elapsed = elapsed_micros(start)

expect(probe.roundtrip_count).to_equal(13)
expect(elapsed).to_be_less_than(25000)
```

</details>

#### activates the built-in launcher command within the warm NFR budget

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val warmup = office_action_dispatch("open_word", "")
expect(warmup.reason).to_equal("opened")

val start = rt_time_now_unix_micros()
val result = office_action_dispatch("open_word", "")
val elapsed = elapsed_micros(start)

expect(result.reason).to_equal("opened")
expect(elapsed).to_be_less_than(50000)
```

</details>

#### keeps hot built-in command dispatch under the p95 budget

<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val warmup = office_action_dispatch("open_word", "")
expect(warmup.reason).to_equal("opened")

val start = rt_time_now_unix_micros()
val a = office_action_dispatch("open_word", "")
val b = office_action_dispatch("open_word", "")
val c = office_action_dispatch("open_word", "")
val d = office_action_dispatch("open_word", "")
val e = office_action_dispatch("open_word", "")
val elapsed = elapsed_micros(start)

expect(a.reason).to_equal("opened")
expect(b.reason).to_equal("opened")
expect(c.reason).to_equal("opened")
expect(d.reason).to_equal("opened")
expect(e.reason).to_equal("opened")
expect(elapsed / 5).to_be_less_than(2000)
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

- **Requirements:** [doc/02_requirements/nfr/ide_plugin_architecture.md](doc/02_requirements/nfr/ide_plugin_architecture.md)
- **Plan:** [doc/03_plan/sys_test/ide_office_plugin_suite.md](doc/03_plan/sys_test/ide_office_plugin_suite.md)


</details>
