# test_daemon_gui_routing_spec

> Test Daemon GUI Routing Specification

<!-- sdn-diagram:id=test_daemon_gui_routing_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=test_daemon_gui_routing_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

test_daemon_gui_routing_spec -> std
test_daemon_gui_routing_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=test_daemon_gui_routing_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 20 | 20 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# test_daemon_gui_routing_spec

Test Daemon GUI Routing Specification

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #TDMN-GUI-01 to #TDMN-GUI-15 |
| Category | Infrastructure |
| Status | Active |
| Source | `test/01_unit/app/test_daemon/test_daemon_gui_routing_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Test Daemon GUI Routing Specification

Verifies GUI test path classification, session key mapping,
mode normalization, and QEMU architecture inference using the
actual gui_adapter implementation.

## Scenarios

### TestDaemon GUI routing

### GUI path detection

#### treats system gui specs as GUI tests

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_gui_test_path("test/system/gui/widget_rendering_spec.spl")).to_equal(true)
```

</details>

#### treats unit app ui specs as GUI tests

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_gui_test_path("test/unit/app/ui/unified_app_spec.spl")).to_equal(true)
```

</details>

#### treats .ui.sdn files as GUI targets

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_gui_test_path("examples/06_io/ui/minimal.ui.sdn")).to_equal(true)
```

</details>

#### treats app/ui paths as GUI tests

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_gui_test_path("src/app/ui/main_window.spl")).to_equal(true)
```

</details>

#### does not treat non-gui specs as GUI tests

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_gui_test_path("test/system/test_daemon/test_daemon_flow_system_spec.spl")).to_equal(false)
```

</details>

#### does not treat plain spl files as GUI tests

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_gui_test_path("test/unit/parser/lexer_spec.spl")).to_equal(false)
```

</details>

### session key mapping

#### maps system gui tests to shared system key

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val key = gui_session_key_for_path("test/system/gui/unified_app_spec.spl")
expect(key).to_equal("system_gui")
```

</details>

#### maps unit app ui tests to shared unit key

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val key = gui_session_key_for_path("test/unit/app/ui/theme_spec.spl")
expect(key).to_equal("unit_ui")
```

</details>

#### falls back to path for unknown gui locations

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = "tmp/custom/gui_like_spec.spl"
val key = gui_session_key_for_path(path)
expect(key).to_equal(path)
```

</details>

### mode normalization

#### accepts container mode

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(normalize_gui_mode("container")).to_equal("container")
```

</details>

#### maps headed/native to native

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(normalize_gui_mode("headed")).to_equal("native")
expect(normalize_gui_mode("native")).to_equal("native")
```

</details>

#### maps none/headless/any to headless

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(normalize_gui_mode("none")).to_equal("headless")
expect(normalize_gui_mode("headless")).to_equal("headless")
expect(normalize_gui_mode("any")).to_equal("headless")
```

</details>

#### returns empty for unknown mode

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(normalize_gui_mode("weird_mode")).to_equal("")
```

</details>

### QEMU arch inference

#### infers riscv64 from path

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(infer_qemu_arch("test/feature/baremetal/riscv64_boot_spec.spl")).to_equal("riscv64")
```

</details>

#### infers riscv32 from path

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(infer_qemu_arch("test/feature/baremetal/riscv32_blink_spec.spl")).to_equal("riscv32")
```

</details>

#### infers arm64 from path

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(infer_qemu_arch("test/feature/baremetal/arm64_boot_spec.spl")).to_equal("arm64")
```

</details>

#### infers aarch64 as arm64

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(infer_qemu_arch("test/feature/baremetal/aarch64_uart_spec.spl")).to_equal("arm64")
```

</details>

#### infers x86_64 from path

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(infer_qemu_arch("test/unit/compiler/native/x86_64_simd_spec.spl")).to_equal("x86_64")
```

</details>

#### infers amd64 as x86_64

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(infer_qemu_arch("test/feature/baremetal/amd64_paging_spec.spl")).to_equal("x86_64")
```

</details>

#### defaults to x86_64 when no arch detected

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(infer_qemu_arch("test/unit/parser/lexer_spec.spl")).to_equal("x86_64")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 20 |
| Active scenarios | 20 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
