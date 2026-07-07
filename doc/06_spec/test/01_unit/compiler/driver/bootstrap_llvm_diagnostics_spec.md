# Bootstrap Llvm Diagnostics Specification

> <details>

<!-- sdn-diagram:id=bootstrap_llvm_diagnostics_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=bootstrap_llvm_diagnostics_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

bootstrap_llvm_diagnostics_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=bootstrap_llvm_diagnostics_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Bootstrap Llvm Diagnostics Specification

## Scenarios

### Bootstrap LLVM diagnostics

#### derives the temporary IR path from the bootstrap object path

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val obj_path = "/tmp/simple_llvm_4242.o"
val ir_path = bootstrap_llvm_ir_path_from_object_path(obj_path)

expect(ir_path).to_equal("/tmp/simple_llvm_4242.ll")
```

</details>

#### labels llc, object, worker, and link failures distinctly

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val llc_msg = bootstrap_llvm_phase_message("llc", "ir=/tmp/simple_llvm_4242.ll obj=/tmp/simple_llvm_4242.o", "llc failed during bootstrap")
val object_msg = bootstrap_llvm_phase_message("object", "source=/tmp/simple_llvm_4242.o dest=/tmp/out.o", "Bootstrap backend did not preserve an object file")
val worker_msg = bootstrap_llvm_phase_message("worker", "backend=llvm output=/tmp/out.o", "backend worker exited with code 1")
val link_msg = bootstrap_llvm_phase_message("link", "input=/tmp/out.o output=/tmp/out", "ld failed")

expect(llc_msg).to_equal("Bootstrap LLVM llc failed (ir=/tmp/simple_llvm_4242.ll obj=/tmp/simple_llvm_4242.o): llc failed during bootstrap")
expect(object_msg).to_equal("Bootstrap LLVM object failed (source=/tmp/simple_llvm_4242.o dest=/tmp/out.o): Bootstrap backend did not preserve an object file")
expect(worker_msg).to_equal("Bootstrap LLVM worker failed (backend=llvm output=/tmp/out.o): backend worker exited with code 1")
expect(link_msg).to_equal("Bootstrap LLVM link failed (input=/tmp/out.o output=/tmp/out): ld failed")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/driver/bootstrap_llvm_diagnostics_spec.spl` |
| Updated | 2026-07-06 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Bootstrap LLVM diagnostics

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
