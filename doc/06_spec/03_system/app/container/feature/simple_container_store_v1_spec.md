# Simple Container Store V1 Specification

> Tests covering simple container shared immutable store.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Simple Container Store V1 Specification

## Scenarios

### simple container shared immutable store

#### shares base objects between two container clients with zero new payload bytes

- Initialize one shared store root for both container clients
- Client 1 ingests the base file set
   - Expected: base_hostname.status equals `ok`
   - Expected: base_hostname.reused is false
   - Expected: base_app.reused is false
   - Expected: base_config.reused is false
- Client 1 publishes the shared root at generation 0
   - Expected: immutable_store_v1_publish_root(root, "shared", base_manifest, 0) equals ``
   - Expected: _count_objects(root) equals `3`
- Client 2 resolves the same base objects by digest
   - Expected: again_hostname.reused is true
   - Expected: again_hostname.object_key equals `base_hostname.object_key`
   - Expected: again_app.reused is true
   - Expected: again_app.object_key equals `base_app.object_key`
   - Expected: again_config.reused is true
   - Expected: again_config.object_key equals `base_config.object_key`
- Verify client 2 wrote zero new payload bytes
   - Expected: _count_objects(root) equals `3`
- Client 2 saves an edit as a new object and advances the shared root to generation 1
   - Expected: edited.status equals `ok`
   - Expected: edited.reused is false
   - Expected: edited.object_key == base_config.object_key is false
   - Expected: _count_objects(root) equals `4`
   - Expected: immutable_store_v1_publish_root(root, "shared", work_manifest, 1) equals ``
- Reject a stale root writer and a second create-only publish
- Client 2 publishes its own work root at generation 0
   - Expected: immutable_store_v1_publish_root(root, "client2-work", work_manifest, 0) equals ``
- Ingest a deliberately orphaned object
   - Expected: orphan.status equals `ok`
   - Expected: _count_objects(root) equals `5`
- Dry-run GC lists the orphan without moving anything
   - Expected: dry.status equals `ok`
   - Expected: dry.moved equals `0`
   - Expected: dry.unreachable.len() equals `1`
   - Expected: dry.unreachable[0] equals `orphan.object_key`
   - Expected: _count_objects(root) equals `5`
- Prune quarantines the orphan and keeps everything reachable from both roots
   - Expected: pruned.status equals `ok`
   - Expected: pruned.moved equals `1`
   - Expected: immutable_store_v1_open(root, orphan.object_key).status equals `missing`
   - Expected: immutable_store_v1_open(root, base_hostname.object_key).status equals `ok`
   - Expected: immutable_store_v1_open(root, base_app.object_key).status equals `ok`
   - Expected: immutable_store_v1_open(root, base_config.object_key).status equals `ok`
   - Expected: immutable_store_v1_open(root, edited.object_key).status equals `ok`
   - Expected: _count_objects(root) equals `4`
   - Expected: quarantine_dates.len() equals `1`
   - Expected: file_exists(quarantine + "/" + orphan.object_key + ".obj") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 69 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Initialize one shared store root for both container clients")
val root = _store_root("shared")
step("Client 1 ingests the base file set")
val base_hostname = immutable_store_v1_ingest(root, "container-a\n".bytes(), HASH_POLICY_V1_XXH3_128)
val base_app = immutable_store_v1_ingest(root, "elf-bytes-v1".bytes(), HASH_POLICY_V1_XXH3_128)
val base_config = immutable_store_v1_ingest(root, "key=value\n".bytes(), HASH_POLICY_V1_XXH3_128)
expect(base_hostname.status).to_equal("ok")
expect(base_hostname.reused).to_equal(false)
expect(base_app.reused).to_equal(false)
expect(base_config.reused).to_equal(false)
val base_manifest = base_hostname.object_key + "\n" + base_app.object_key + "\n" +
    base_config.object_key + "\n"
step("Client 1 publishes the shared root at generation 0")
expect(immutable_store_v1_publish_root(root, "shared", base_manifest, 0)).to_equal("")
expect(_count_objects(root)).to_equal(3)
step("Client 2 resolves the same base objects by digest")
val again_hostname = immutable_store_v1_ingest(root, "container-a\n".bytes(), HASH_POLICY_V1_XXH3_128)
val again_app = immutable_store_v1_ingest(root, "elf-bytes-v1".bytes(), HASH_POLICY_V1_XXH3_128)
val again_config = immutable_store_v1_ingest(root, "key=value\n".bytes(), HASH_POLICY_V1_XXH3_128)
expect(again_hostname.reused).to_equal(true)
expect(again_hostname.object_key).to_equal(base_hostname.object_key)
expect(again_app.reused).to_equal(true)
expect(again_app.object_key).to_equal(base_app.object_key)
expect(again_config.reused).to_equal(true)
expect(again_config.object_key).to_equal(base_config.object_key)
step("Verify client 2 wrote zero new payload bytes")
expect(_count_objects(root)).to_equal(3)
step("Client 2 saves an edit as a new object and advances the shared root to generation 1")
val edited = immutable_store_v1_ingest(root, "key=value\nmotd=hello\n".bytes(), HASH_POLICY_V1_XXH3_128)
expect(edited.status).to_equal("ok")
expect(edited.reused).to_equal(false)
expect(edited.object_key == base_config.object_key).to_equal(false)
expect(_count_objects(root)).to_equal(4)
val work_manifest = base_hostname.object_key + "\n" + base_app.object_key + "\n" +
    base_config.object_key + "\n" + edited.object_key + "\n"
expect(immutable_store_v1_publish_root(root, "shared", work_manifest, 1)).to_equal("")
step("Reject a stale root writer and a second create-only publish")
expect(immutable_store_v1_publish_root(root, "shared", base_manifest, 1)).to_equal(
    "root-generation-mismatch")
expect(immutable_store_v1_publish_root(root, "shared", base_manifest, 0)).to_equal(
    "root-exists")
step("Client 2 publishes its own work root at generation 0")
expect(immutable_store_v1_publish_root(root, "client2-work", work_manifest, 0)).to_equal("")
step("Ingest a deliberately orphaned object")
val orphan = immutable_store_v1_ingest(root, "orphan-scratch\n".bytes(), HASH_POLICY_V1_XXH3_128)
expect(orphan.status).to_equal("ok")
expect(_count_objects(root)).to_equal(5)
step("Dry-run GC lists the orphan without moving anything")
val dry = immutable_store_v1_collect(root, true)
expect(dry.status).to_equal("ok")
expect(dry.moved).to_equal(0)
expect(dry.unreachable.len()).to_equal(1)
expect(dry.unreachable[0]).to_equal(orphan.object_key)
expect(_count_objects(root)).to_equal(5)
step("Prune quarantines the orphan and keeps everything reachable from both roots")
val pruned = immutable_store_v1_collect(root, false)
expect(pruned.status).to_equal("ok")
expect(pruned.moved).to_equal(1)
expect(immutable_store_v1_open(root, orphan.object_key).status).to_equal("missing")
expect(immutable_store_v1_open(root, base_hostname.object_key).status).to_equal("ok")
expect(immutable_store_v1_open(root, base_app.object_key).status).to_equal("ok")
expect(immutable_store_v1_open(root, base_config.object_key).status).to_equal("ok")
expect(immutable_store_v1_open(root, edited.object_key).status).to_equal("ok")
expect(_count_objects(root)).to_equal(4)
val quarantine_dates = dir_list(root + "/quarantine")
expect(quarantine_dates.len()).to_equal(1)
val quarantine = root + "/quarantine/" + quarantine_dates[0].trim()
expect(file_exists(quarantine + "/" + orphan.object_key + ".obj")).to_equal(true)
_store_cleanup(root)
```

</details>

#### admits a linux cgroup report and rejects a macOS report without memory hard limit evidence

- Admit a linux cgroup capability report against a strict requirement
- Reject a macOS-like report without memory hard limit evidence
- Reject unknown memory accounting evidence fail-closed


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Admit a linux cgroup capability report against a strict requirement")
var requirement = container_capability_requirement_v1_empty()
requirement.required_host_os = "linux"
requirement.required_isolation_kind = CONTAINER_ISOLATION_KIND_NATIVE_V1
requirement.required_launch_qualified = true
requirement.required_memory_accounting = CONTAINER_MEMORY_ACCOUNTING_CGROUP_V1
requirement.required_memory_hard_limit = true
expect(container_capability_v1_admission_reason(_linux_cgroup_report(),
    requirement)).to_equal("")
step("Reject a macOS-like report without memory hard limit evidence")
var macos_requirement = container_capability_requirement_v1_empty()
macos_requirement.required_host_os = "macos"
macos_requirement.required_isolation_kind = CONTAINER_ISOLATION_KIND_NATIVE_SANDBOX_V1
macos_requirement.required_memory_hard_limit = true
expect(container_capability_v1_admission_reason(_macos_sandbox_report(),
    macos_requirement)).to_equal("memory-hard-limit-missing")
step("Reject unknown memory accounting evidence fail-closed")
var unknown_accounting = _macos_sandbox_report()
unknown_accounting.memory_accounting = "vm-pressure"
expect(container_capability_v1_admission_reason(unknown_accounting,
    macos_requirement)).to_equal("capability-report-memory-accounting-unknown")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/03_system/app/container/feature/simple_container_store_v1_spec.spl` |
| Updated | 2026-11-25 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering simple container shared immutable store.
- simple container shared immutable store

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
