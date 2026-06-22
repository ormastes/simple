# test_daemon_session_config_spec

> @cover src/lib/nogc_sync_mut/test_runner/test_config.spl 80%

<!-- sdn-diagram:id=test_daemon_session_config_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=test_daemon_session_config_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

test_daemon_session_config_spec -> std
test_daemon_session_config_spec -> test_config
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=test_daemon_session_config_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 22 | 22 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# test_daemon_session_config_spec

@cover src/lib/nogc_sync_mut/test_runner/test_config.spl 80%

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #TDMN-CFG-001 to #TDMN-CFG-015 |
| Category | Infrastructure |
| Status | Active |
| Source | `test/01_unit/app/test_daemon/test_daemon_session_config_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

@cover src/lib/nogc_sync_mut/test_runner/test_config.spl 80%
@cover src/app/test_daemon/session_types.spl 40%

Test Daemon Session Config Specification

Tests that session sharing settings are correctly loaded from SDN config
and correctly propagated to TestDaemonConfig.

## Scenarios

### Session Config Defaults

#### defaults session_share to false (#TDMN-CFG-001)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = TestConfig.defaults()
expect(config.session_share).to_equal(false)
```

</details>

#### defaults session_daemon to false (#TDMN-CFG-002)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = TestConfig.defaults()
expect(config.session_daemon).to_equal(false)
```

</details>

#### defaults session_idle_timeout_ms to 300000 (#TDMN-CFG-003)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = TestConfig.defaults()
expect(config.session_idle_timeout_ms).to_equal(300000)
```

</details>

#### defaults session_startup_timeout_ms to 60000 (#TDMN-CFG-004)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = TestConfig.defaults()
expect(config.session_startup_timeout_ms).to_equal(60000)
```

</details>

#### defaults session_debug to false (#TDMN-CFG-005)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = TestConfig.defaults()
expect(config.session_debug).to_equal(false)
```

</details>

#### defaults session_max_qemu_vm to 4 (#TDMN-CFG-006)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = TestConfig.defaults()
expect(config.session_max_qemu_vm).to_equal(4)
```

</details>

#### defaults session_max_container to 2 (#TDMN-CFG-007)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = TestConfig.defaults()
expect(config.session_max_container).to_equal(2)
```

</details>

#### defaults session_max_service to 8 (#TDMN-CFG-008)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = TestConfig.defaults()
expect(config.session_max_service).to_equal(8)
```

</details>

#### defaults session_max_openocd to 1 (#TDMN-CFG-009)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = TestConfig.defaults()
expect(config.session_max_openocd).to_equal(1)
```

</details>

#### defaults session_max_trace32 to 1 (#TDMN-CFG-010)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = TestConfig.defaults()
expect(config.session_max_trace32).to_equal(1)
```

</details>

### Session Config SDN Parsing

#### parses session_share: true (#TDMN-CFG-011)

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sdn = "test:\n  session_share: true\n"
val config = TestConfig.defaults()
val result = parse_test_config_content(config, sdn)
expect(result.session_share).to_equal(true)
```

</details>

#### parses session_daemon: true (#TDMN-CFG-012)

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sdn = "test:\n  session_daemon: true\n"
val config = TestConfig.defaults()
val result = parse_test_config_content(config, sdn)
expect(result.session_daemon).to_equal(true)
```

</details>

#### parses session_idle_timeout_ms (#TDMN-CFG-013)

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sdn = "test:\n  session_idle_timeout_ms: 120000\n"
val config = TestConfig.defaults()
val result = parse_test_config_content(config, sdn)
expect(result.session_idle_timeout_ms).to_equal(120000)
```

</details>

#### parses session_startup_timeout_ms (#TDMN-CFG-014)

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sdn = "test:\n  session_startup_timeout_ms: 30000\n"
val config = TestConfig.defaults()
val result = parse_test_config_content(config, sdn)
expect(result.session_startup_timeout_ms).to_equal(30000)
```

</details>

#### parses session_debug: true (#TDMN-CFG-015)

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sdn = "test:\n  session_debug: true\n"
val config = TestConfig.defaults()
val result = parse_test_config_content(config, sdn)
expect(result.session_debug).to_equal(true)
```

</details>

### Session Config Max Sessions Parsing

#### parses qemu_vm max from session_max_sessions (#TDMN-CFG-016)

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sdn = "test:\n  session_max_sessions:\n    qemu_vm: 8\n"
val config = TestConfig.defaults()
val result = parse_test_config_content(config, sdn)
expect(result.session_max_qemu_vm).to_equal(8)
```

</details>

#### parses container_instance max (#TDMN-CFG-017)

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sdn = "test:\n  session_max_sessions:\n    container_instance: 5\n"
val config = TestConfig.defaults()
val result = parse_test_config_content(config, sdn)
expect(result.session_max_container).to_equal(5)
```

</details>

#### parses service_process max (#TDMN-CFG-018)

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sdn = "test:\n  session_max_sessions:\n    service_process: 16\n"
val config = TestConfig.defaults()
val result = parse_test_config_content(config, sdn)
expect(result.session_max_service).to_equal(16)
```

</details>

#### parses multiple max_sessions keys in one block (#TDMN-CFG-019)

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sdn = "test:\n  session_max_sessions:\n    qemu_vm: 6\n    container_instance: 3\n    trace32_board: 2\n"
val config = TestConfig.defaults()
val result = parse_test_config_content(config, sdn)
expect(result.session_max_qemu_vm).to_equal(6)
expect(result.session_max_container).to_equal(3)
expect(result.session_max_trace32).to_equal(2)
```

</details>

### Session Config Mixed Sections

#### parses session settings alongside test timeout (#TDMN-CFG-020)

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sdn = "test:\n  timeout: 240\n  session_share: true\n  session_idle_timeout_ms: 600000\n"
val config = TestConfig.defaults()
val result = parse_test_config_content(config, sdn)
expect(result.timeout_seconds).to_equal(240)
expect(result.session_share).to_equal(true)
expect(result.session_idle_timeout_ms).to_equal(600000)
```

</details>

#### preserves defaults for unparsed session keys (#TDMN-CFG-021)

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sdn = "test:\n  session_share: true\n"
val config = TestConfig.defaults()
val result = parse_test_config_content(config, sdn)
expect(result.session_share).to_equal(true)
# Unparsed keys should retain defaults
expect(result.session_idle_timeout_ms).to_equal(300000)
expect(result.session_max_qemu_vm).to_equal(4)
expect(result.session_debug).to_equal(false)
```

</details>

#### ignores session_defaults sub-section without error (#TDMN-CFG-022)

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sdn = "test:\n  session_share: true\n  session_defaults:\n    qemu_vm:\n      reuse: shared_with_snapshot\n      reset: snapshot_restore\n"
val config = TestConfig.defaults()
val result = parse_test_config_content(config, sdn)
# Should not crash and session_share should be parsed
expect(result.session_share).to_equal(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 22 |
| Active scenarios | 22 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
