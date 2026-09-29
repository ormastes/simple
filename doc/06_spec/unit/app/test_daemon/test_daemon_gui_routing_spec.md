# Test Daemon Gui Routing Specification

> Tests covering TestDaemon GUI routing, GUI path detection, session key mapping, mode normalization, QEMU arch inference.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 20 | 20 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Test Daemon Gui Routing Specification

## Scenarios

### TestDaemon GUI routing

### GUI path detection

#### treats system gui specs as GUI tests

- treats system gui specs as GUI tests
   - Expected: is_gui_test_path("test/system/gui/widget_rendering_spec.spl") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("treats system gui specs as GUI tests")
expect(is_gui_test_path("test/system/gui/widget_rendering_spec.spl")).to_equal(true)
```

</details>

#### treats unit app ui specs as GUI tests

- treats unit app ui specs as GUI tests
   - Expected: is_gui_test_path("test/unit/app/ui/unified_app_spec.spl") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("treats unit app ui specs as GUI tests")
expect(is_gui_test_path("test/unit/app/ui/unified_app_spec.spl")).to_equal(true)
```

</details>

#### treats .ui.sdn files as GUI targets

- treats .ui.sdn files as GUI targets
   - Expected: is_gui_test_path("examples/06_io/ui/minimal.ui.sdn") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("treats .ui.sdn files as GUI targets")
expect(is_gui_test_path("examples/06_io/ui/minimal.ui.sdn")).to_equal(true)
```

</details>

#### treats app/ui paths as GUI tests

- treats app/ui paths as GUI tests
   - Expected: is_gui_test_path("src/app/ui/main_window.spl") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("treats app/ui paths as GUI tests")
expect(is_gui_test_path("src/app/ui/main_window.spl")).to_equal(true)
```

</details>

#### does not treat non-gui specs as GUI tests

- does not treat non-gui specs as GUI tests
   - Expected: is_gui_test_path("test/system/test_daemon/test_daemon_flow_system_spec.spl") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does not treat non-gui specs as GUI tests")
expect(is_gui_test_path("test/system/test_daemon/test_daemon_flow_system_spec.spl")).to_equal(false)
```

</details>

#### does not treat plain spl files as GUI tests

- does not treat plain spl files as GUI tests
   - Expected: is_gui_test_path("test/unit/parser/lexer_spec.spl") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does not treat plain spl files as GUI tests")
expect(is_gui_test_path("test/unit/parser/lexer_spec.spl")).to_equal(false)
```

</details>

### session key mapping

#### maps system gui tests to shared system key

- maps system gui tests to shared system key
   - Expected: key equals `system_gui`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("maps system gui tests to shared system key")
val key = gui_session_key_for_path("test/system/gui/unified_app_spec.spl")
expect(key).to_equal("system_gui")
```

</details>

#### maps unit app ui tests to shared unit key

- maps unit app ui tests to shared unit key
   - Expected: key equals `unit_ui`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("maps unit app ui tests to shared unit key")
val key = gui_session_key_for_path("test/unit/app/ui/theme_spec.spl")
expect(key).to_equal("unit_ui")
```

</details>

#### falls back to path for unknown gui locations

- falls back to path for unknown gui locations
   - Expected: key equals `path`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("falls back to path for unknown gui locations")
val path = "tmp/custom/gui_like_spec.spl"
val key = gui_session_key_for_path(path)
expect(key).to_equal(path)
```

</details>

### mode normalization

#### accepts container mode

- accepts container mode
   - Expected: normalize_gui_mode("container") equals `container`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("accepts container mode")
expect(normalize_gui_mode("container")).to_equal("container")
```

</details>

#### maps headed/native to native

- maps headed/native to native
   - Expected: normalize_gui_mode("headed") equals `native`
   - Expected: normalize_gui_mode("native") equals `native`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("maps headed/native to native")
expect(normalize_gui_mode("headed")).to_equal("native")
expect(normalize_gui_mode("native")).to_equal("native")
```

</details>

#### maps none/headless/any to headless

- maps none/headless/any to headless
   - Expected: normalize_gui_mode("none") equals `headless`
   - Expected: normalize_gui_mode("headless") equals `headless`
   - Expected: normalize_gui_mode("any") equals `headless`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("maps none/headless/any to headless")
expect(normalize_gui_mode("none")).to_equal("headless")
expect(normalize_gui_mode("headless")).to_equal("headless")
expect(normalize_gui_mode("any")).to_equal("headless")
```

</details>

#### returns empty for unknown mode

- returns empty for unknown mode
   - Expected: normalize_gui_mode("weird_mode") equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns empty for unknown mode")
expect(normalize_gui_mode("weird_mode")).to_equal("")
```

</details>

### QEMU arch inference

#### infers riscv64 from path

- infers riscv64 from path
   - Expected: infer_qemu_arch("test/feature/baremetal/riscv64_boot_spec.spl") equals `riscv64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("infers riscv64 from path")
expect(infer_qemu_arch("test/feature/baremetal/riscv64_boot_spec.spl")).to_equal("riscv64")
```

</details>

#### infers riscv32 from path

- infers riscv32 from path
   - Expected: infer_qemu_arch("test/feature/baremetal/riscv32_blink_spec.spl") equals `riscv32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("infers riscv32 from path")
expect(infer_qemu_arch("test/feature/baremetal/riscv32_blink_spec.spl")).to_equal("riscv32")
```

</details>

#### infers arm64 from path

- infers arm64 from path
   - Expected: infer_qemu_arch("test/feature/baremetal/arm64_boot_spec.spl") equals `arm64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("infers arm64 from path")
expect(infer_qemu_arch("test/feature/baremetal/arm64_boot_spec.spl")).to_equal("arm64")
```

</details>

#### infers aarch64 as arm64

- infers aarch64 as arm64
   - Expected: infer_qemu_arch("test/feature/baremetal/aarch64_uart_spec.spl") equals `arm64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("infers aarch64 as arm64")
expect(infer_qemu_arch("test/feature/baremetal/aarch64_uart_spec.spl")).to_equal("arm64")
```

</details>

#### infers x86_64 from path

- infers x86_64 from path
   - Expected: infer_qemu_arch("test/unit/compiler/native/x86_64_simd_spec.spl") equals `x86_64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("infers x86_64 from path")
expect(infer_qemu_arch("test/unit/compiler/native/x86_64_simd_spec.spl")).to_equal("x86_64")
```

</details>

#### infers amd64 as x86_64

- infers amd64 as x86_64
   - Expected: infer_qemu_arch("test/feature/baremetal/amd64_paging_spec.spl") equals `x86_64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("infers amd64 as x86_64")
expect(infer_qemu_arch("test/feature/baremetal/amd64_paging_spec.spl")).to_equal("x86_64")
```

</details>

#### defaults to x86_64 when no arch detected

- defaults to x86_64 when no arch detected
   - Expected: infer_qemu_arch("test/unit/parser/lexer_spec.spl") equals `x86_64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("defaults to x86_64 when no arch detected")
expect(infer_qemu_arch("test/unit/parser/lexer_spec.spl")).to_equal("x86_64")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/unit/app/test_daemon/test_daemon_gui_routing_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering TestDaemon GUI routing, GUI path detection, session key mapping, mode normalization, QEMU arch inference.
- TestDaemon GUI routing
- GUI path detection
- session key mapping
- mode normalization
- QEMU arch inference

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 20 |
| Active scenarios | 20 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `e753f98117b04e276af53cc23bc32a09b2bfb444528bfe60bc8dbf27206993ba`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `e753f98117b04e276af53cc23bc32a09b2bfb444528bfe60bc8dbf27206993ba`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `e753f98117b04e276af53cc23bc32a09b2bfb444528bfe60bc8dbf27206993ba`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/app/test_daemon/test_daemon_gui_routing_spec.spl
mirror: doc/06_spec/unit/app/test_daemon/test_daemon_gui_routing_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/app/test_daemon/test_daemon_gui_routing_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/app/test_daemon/test_daemon_gui_routing_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/app/test_daemon/test_daemon_gui_routing_spec.spl:27:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'treats system gui specs as GUI tests' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/test_daemon/test_daemon_gui_routing_spec.spl:32:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'treats unit app ui specs as GUI tests' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/test_daemon/test_daemon_gui_routing_spec.spl:37:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'treats .ui.sdn files as GUI targets' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
