# Runtime Backend Boundaries Audit Specification

> <details>

<!-- sdn-diagram:id=runtime_backend_boundaries_audit_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=runtime_backend_boundaries_audit_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

runtime_backend_boundaries_audit_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=runtime_backend_boundaries_audit_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Runtime Backend Boundaries Audit Specification

## Scenarios

### runtime backend boundary audit

#### passes clean roots and fails each guarded boundary class

<details>
<summary>Executable SPipe</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "/tmp/simple_runtime_backend_boundaries_spec"
val (_clean_out, _clean_err, _clean_code) = rt_process_run("/bin/sh", ["-c", "rm -rf " + root + " && mkdir -p " + root])

val clean = run_audit(root)
expect(clean.2).to_equal(0)
expect(clean.0).to_contain("\"pass\": true")
expect(clean.0).to_contain("\"async_compat_direct_runtime_hook_count\": 0")

val (_mkdir_out, _mkdir_err, _mkdir_code) = rt_process_run("/bin/sh", ["-c", "mkdir -p " + root + "/src/lib/gc_async_mut " + root + "/src/lib/nogc_async_mut " + root + "/src/lib/nogc_sync_mut " + root + "/src/os/services " + root + "/src/lib/common"])
expect(rt_file_write_text(root + "/src/lib/gc_async_mut/direct.spl", "extern fn rt_file_read_text(path: text) -> text\n")).to_equal(true)
expect(rt_file_write_text(root + "/src/lib/gc_async_mut/facade.spl", "export use std.nogc_sync_mut.backend.*\n")).to_equal(true)
expect(rt_file_write_text(root + "/src/lib/nogc_async_mut/facade.spl", "export use std.nogc_sync_mut.backend.*\n")).to_equal(true)
expect(rt_file_write_text(root + "/src/lib/nogc_sync_mut/backend.spl", "extern fn rt_backend_hook() -> i64\n")).to_equal(true)
expect(rt_file_write_text(root + "/src/os/services/bad.spl", "use os.posix.fd.open\n")).to_equal(true)
expect(rt_file_write_text(root + "/src/lib/common/bad.spl", "use std.linux.fd.open\n")).to_equal(true)

val failed = run_audit(root)
expect(failed.2).to_equal(1)
expect(failed.0).to_contain("\"pass\": false")
expect(failed.0).to_contain("\"async_compat_direct_runtime_hook_count\": 1")
expect(failed.0).to_contain("\"gc_async_runtime_owner_wildcard_facade_count\": 1")
expect(failed.0).to_contain("\"nogc_async_runtime_owner_wildcard_facade_count\": 1")
expect(failed.0).to_contain("\"simpleos_lower_layer_posix_libc_import_count\": 1")
expect(failed.0).to_contain("\"portable_lib_forbidden_posix_linux_import_count\": 1")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/quality/code_quality/runtime_backend_boundaries_audit_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- runtime backend boundary audit

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
