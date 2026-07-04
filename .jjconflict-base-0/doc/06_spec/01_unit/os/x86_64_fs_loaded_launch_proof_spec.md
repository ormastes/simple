# X86 64 Fs Loaded Launch Proof Specification

> <details>

<!-- sdn-diagram:id=x86_64_fs_loaded_launch_proof_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=x86_64_fs_loaded_launch_proof_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

x86_64_fs_loaded_launch_proof_spec -> std
x86_64_fs_loaded_launch_proof_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=x86_64_fs_loaded_launch_proof_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# X86 64 Fs Loaded Launch Proof Specification

## Scenarios

### x86_64 fs-loaded launch proof

#### accepts direct filesystem process-backed tool app proof

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val serial = process_backed_tool_app_serial()
val proofs = classify_all_tool_app_proofs(serial)

expect(proofs.len()).to_equal(6)
expect(all_tool_apps_have_base_proof(serial)).to_equal(true)
expect(tool_apps_serial_accepts_completion(serial)).to_equal(true)
expect(has_resident_manifest_fallback(serial)).to_equal(false)
```

</details>

#### rejects resident-manifest fallback as completion evidence

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val serial = resident_manifest_fallback_serial()
val proofs = classify_all_tool_app_proofs(serial)

expect(proofs.len()).to_equal(6)
expect(has_resident_manifest_fallback(serial)).to_equal(true)
expect(all_tool_apps_have_base_proof(serial)).to_equal(false)
expect(tool_apps_serial_accepts_completion(serial)).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/x86_64_fs_loaded_launch_proof_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- x86_64 fs-loaded launch proof

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
