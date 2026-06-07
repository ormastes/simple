# Wine Hello Exe Specification

> <details>

<!-- sdn-diagram:id=wine_hello_exe_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=wine_hello_exe_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

wine_hello_exe_spec -> common
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=wine_hello_exe_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 13 | 13 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Wine Hello Exe Specification

## Scenarios

### Wine hello.exe probe

#### blocks before all substrate gates are verified

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = wine_hello_exe_probe(_minimal_pe64_console_with_dirs(), "process=verified exec_env=verified vm=verified")
expect(result.status).to_equal("blocked")
expect(result.error).to_equal("blocked")
```

</details>

#### rejects malformed PE data after gates are verified

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = wine_hello_exe_probe([], _verified_gates())
expect(result.status).to_equal("rejected")
expect(result.error).to_equal("too-small")
expect(wine_hello_exe_can_execute([], _verified_gates())).to_equal(false)
```

</details>

#### stops at structured import resolution instead of unsafe execution

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = wine_hello_exe_probe(_minimal_pe64_console_with_import_descriptor(), _verified_gates())
expect(result.status).to_equal("unsupported-import")
expect(result.error).to_equal("import-thunk-ordinal-unsupported")
```

</details>

#### reaches the CPU precondition boundary after minimal imports and image layout resolve

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = wine_hello_exe_probe(_minimal_pe64_console_with_resolved_imports(), _verified_gates())
expect(result.status).to_equal("blocked")
expect(result.error).to_equal("missing-thread-context")
```

</details>

#### rejects import binding targets that do not match the decoded hello calls

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = wine_hello_exe_probe(_known_hello_exe_with_mismatched_write_binding(), _verified_dispatch_gates())
expect(result.status).to_equal("unsupported-import")
expect(result.error).to_equal("binding-target-mismatch:WriteFile")
```

</details>

#### rejects malformed import thunk name RVAs before resolver checks

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = wine_hello_exe_probe(_known_hello_exe_with_unmapped_import_name(), _verified_dispatch_gates())
expect(result.status).to_equal("unsupported-import")
expect(result.error).to_equal("import-symbol-name-unmapped")
```

</details>

#### reaches the instruction decoder boundary after CPU execution preconditions resolve

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = wine_hello_exe_probe(_minimal_pe64_console_with_resolved_imports(), _verified_cpu_envelope_gates())
expect(result.status).to_equal("blocked")
expect(result.error).to_equal("instruction-decoder-missing")
```

</details>

#### requires the decoded stdout payload after dispatch resolves

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = wine_hello_exe_probe(_known_hello_exe_without_marker(), _verified_dispatch_gates())
expect(result.status).to_equal("blocked")
expect(result.error).to_equal("hello-stdout-payload-rva-mismatch")
```

</details>

#### executes the decoded hello stdout payload without a fixture marker

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = wine_hello_exe_probe(_known_hello_exe_with_payload_without_marker(), _verified_dispatch_gates())
expect(result.status).to_equal("executed")
expect(result.stdout).to_equal("Hello from SimpleOS Wine\n")
```

</details>

#### executes the decoded hello stdout payload after a safe entry prologue

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = wine_hello_exe_probe(_known_hello_exe_with_safe_prologue(), _verified_dispatch_gates())
expect(result.status).to_equal("executed")
expect(result.stdout).to_equal("Hello from SimpleOS Wine\n")
```

</details>

#### requires fixture stdout payload bytes after the marker

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = wine_hello_exe_probe(_known_hello_exe_without_payload(), _verified_dispatch_gates())
expect(result.status).to_equal("blocked")
expect(result.error).to_equal("hello-stdout-payload-rva-mismatch")
expect(wine_hello_stdout_payload_gate_at_rva(_known_hello_exe_without_payload(), 0x2120)).to_equal("hello-stdout-payload-rva-mismatch")
```

</details>

#### requires the known hello instruction skeleton after dispatch resolves

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = wine_hello_exe_probe(_minimal_pe64_console_with_resolved_imports(), _verified_dispatch_gates())
expect(result.status).to_equal("blocked")
expect(result.error).to_equal("unsupported-entry-instruction:unsupported-opcode")
```

</details>

#### executes the known non-GUI hello.exe milestone fixture

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = wine_hello_exe_probe(_known_hello_exe_fixture(), _verified_dispatch_gates())
expect(result.status).to_equal("executed")
expect(result.stdout).to_equal("Hello from SimpleOS Wine\n")
expect(result.stdout_handle).to_equal(-11)
expect(result.bytes_written).to_equal(25)
expect(result.exit_code).to_equal(0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/wine_hello_exe_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Wine hello.exe probe

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 13 |
| Active scenarios | 13 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
