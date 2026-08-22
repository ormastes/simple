# Host Win-FS shim Specification

> Verifies the winfs shim host behaviour end to end so maintainers of this

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Host Win-FS shim Specification

Verifies the winfs shim host behaviour end to end so maintainers of this

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Red (no impl yet) |
| Source | `test/02_integration/app/simple_process_manager/winfs_shim_host_spec.spl` |
| Updated | 2026-08-22 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Verifies the winfs shim host behaviour end to end so maintainers of this
component and reviewers of its spec share one pinned definition.
## Operator workflow
Run `bin/simple test <this spec>`; read the per-scenario verdicts in
the `Results:` summary. Each scenario asserts an observable outcome.
## Compatibility and limitations
Covers the currently shipped behaviour only; performance, stress and
unrelated sibling features are out of scope.

## Scenarios

### winfs_shim_host

### publish via shared encoder

#### AC-4: publish writes /<app>/<wid>/title under runtime dir

- Verify: AC-4: publish writes /<app>/<wid>/title under runtime dir


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-APP-SIMPLE_PROCESS_MANAGER_WINFS-001
step("Verify: AC-4: publish writes /<app>/<wid>/title under runtime dir")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val shim = WinFsShimHost.new_for_test(runtime_dir: "/tmp/spm_winfs_host")
val rec = WindowRecord(
    wid: 42, generation: 1, app: "banking", title: "Acct",
    state: WindowState.Normal,
    geometry: Rect(x: 0, y: 0, w: 1, h: 1),
    buffer_ref: BufferRef(kind: "shm", handle: 7, bytes: 4096),
    acl_id_path: id_path_intern("id.user.banking.view"))
val result = shim.publish(rec)
expect result.ok to_equal true
val title = read_file("/tmp/spm_winfs_host/banking/42/title")
expect title to_equal "Acct"
```

</details>

#### AC-4: paths match the shared encoder schema (no drift)

- Verify: AC-4: paths match the shared encoder schema (no drift)


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-APP-SIMPLE_PROCESS_MANAGER_WINFS-001
step("Verify: AC-4: paths match the shared encoder schema (no drift)")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val rec = WindowRecord(
    wid: 42, generation: 1, app: "banking", title: "Acct",
    state: WindowState.Normal,
    geometry: Rect(x: 0, y: 0, w: 1, h: 1),
    buffer_ref: BufferRef(kind: "shm", handle: 7, bytes: 4096),
    acl_id_path: id_path_intern("id.user.banking.view"))
val tree = encode_record(rec)
expect tree_has_path(tree, "/banking/42/title") to_equal true
expect tree_has_path(tree, "/banking/42/state") to_equal true
```

</details>

### grep sentinel

#### AC-4: winfs_shim_host.spl imports from common/win_fs/fs_encoder

- Verify: AC-4: winfs_shim_host.spl imports from common/win_fs/fs_encoder


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-APP-SIMPLE_PROCESS_MANAGER_WINFS-001
step("Verify: AC-4: winfs_shim_host.spl imports from common/win_fs/fs_encoder")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val source = read_file("src/app/simple_process_manager/winfs_shim_host.spl")
expect source to_contain "use lib.common.win_fs.fs_encoder"
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

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `a6aeab37b3396e5e619b7c25c2bfde0a9b46a80b258b5894c88bb77239512859`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `a6aeab37b3396e5e619b7c25c2bfde0a9b46a80b258b5894c88bb77239512859`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `a6aeab37b3396e5e619b7c25c2bfde0a9b46a80b258b5894c88bb77239512859`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **94/100**; effective score: **94/100**; blockers: **0**.

SSpec documentization score: 94/100
source: test/02_integration/app/simple_process_manager/winfs_shim_host_spec.spl
mirror: doc/06_spec/02_integration/app/simple_process_manager/winfs_shim_host_spec.md (current)
findings: 3 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=85 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/02_integration/app/simple_process_manager/winfs_shim_host_spec.md:1:1: warning SSDOC-EVD-002 [evidence] (-15): source steps are not visible in the generated manual
  why: Source tokens alone do not prove reader-visible workflow structure.
  improve: Use supported literal step calls and regenerate the manual.
doc/06_spec/02_integration/app/simple_process_manager/winfs_shim_host_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/02_integration/app/simple_process_manager/winfs_shim_host_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: assumptions/preconditions, traceability, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
<!-- sspec-maintain:scorecard:end -->
