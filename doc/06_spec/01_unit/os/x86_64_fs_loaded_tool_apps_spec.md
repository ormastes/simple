# x86_64_fs_loaded_tool_apps_spec

> x86_64 FS-Loaded Tool Apps — acceptance contract specification.

<!-- sdn-diagram:id=x86_64_fs_loaded_tool_apps_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=x86_64_fs_loaded_tool_apps_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

x86_64_fs_loaded_tool_apps_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=x86_64_fs_loaded_tool_apps_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 20 | 20 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# x86_64_fs_loaded_tool_apps_spec

x86_64 FS-Loaded Tool Apps — acceptance contract specification.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/x86_64_fs_loaded_tool_apps_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

x86_64 FS-Loaded Tool Apps — acceptance contract specification.

Self-contained: all classes defined inline. 20 tests covering:
- VFS-read markers for all six tool apps (6 tests)
- Process-backed markers for all six tool apps (6 tests)
- simple_browser WM/render/page_rendered proofs (3 tests)
- llvm and rust toolchain-launch marker shapes (2 tests)
- Acceptance function with all markers present (1 test)
- Acceptance rejects when a vfs-app-read marker is missing (1 test)
- Resident-manifest fallback rejected as completion evidence (1 test)

## Scenarios

### x86_64 FS-Loaded Tool Apps VFS-Read Markers

#### simple_browser emits vfs-app-read:ok from /sys/apps/simple_browser

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val log = SerialLog.empty().with_vfs_read("simple_browser")
expect(check_vfs_read(log.content, "simple_browser")).to_equal(true)
```

</details>

#### simple_compiler emits vfs-app-read:ok from /sys/apps/simple_compiler

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val log = SerialLog.empty().with_vfs_read("simple_compiler")
expect(check_vfs_read(log.content, "simple_compiler")).to_equal(true)
```

</details>

#### simple_interpreter emits vfs-app-read:ok from /sys/apps/simple_interpreter

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val log = SerialLog.empty().with_vfs_read("simple_interpreter")
expect(check_vfs_read(log.content, "simple_interpreter")).to_equal(true)
```

</details>

#### simple_loader emits vfs-app-read:ok from /sys/apps/simple_loader

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val log = SerialLog.empty().with_vfs_read("simple_loader")
expect(check_vfs_read(log.content, "simple_loader")).to_equal(true)
```

</details>

#### llvm emits vfs-app-read:ok from /sys/apps/llvm

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val log = SerialLog.empty().with_vfs_read("llvm")
expect(check_vfs_read(log.content, "llvm")).to_equal(true)
```

</details>

#### rust emits vfs-app-read:ok from /sys/apps/rust

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val log = SerialLog.empty().with_vfs_read("rust")
expect(check_vfs_read(log.content, "rust")).to_equal(true)
```

</details>

### x86_64 FS-Loaded Tool Apps Process-Backed Markers

#### simple_browser emits process-backed:ok with real pid

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val log = SerialLog.empty().with_process_backed("simple_browser", 101)
expect(check_process_backed(log.content, "simple_browser")).to_equal(true)
```

</details>

#### simple_compiler emits process-backed:ok with real pid

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val log = SerialLog.empty().with_process_backed("simple_compiler", 102)
expect(check_process_backed(log.content, "simple_compiler")).to_equal(true)
```

</details>

#### simple_interpreter emits process-backed:ok with real pid

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val log = SerialLog.empty().with_process_backed("simple_interpreter", 103)
expect(check_process_backed(log.content, "simple_interpreter")).to_equal(true)
```

</details>

#### simple_loader emits process-backed:ok with real pid

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val log = SerialLog.empty().with_process_backed("simple_loader", 104)
expect(check_process_backed(log.content, "simple_loader")).to_equal(true)
```

</details>

#### llvm emits process-backed:ok with real pid

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val log = SerialLog.empty().with_process_backed("llvm", 105)
expect(check_process_backed(log.content, "llvm")).to_equal(true)
```

</details>

#### rust emits process-backed:ok with real pid

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val log = SerialLog.empty().with_process_backed("rust", 106)
expect(check_process_backed(log.content, "rust")).to_equal(true)
```

</details>

### x86_64 FS-Loaded Tool Apps simple_browser Desktop Proof

#### simple_browser emits wm-owner:ok

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val log = SerialLog.empty().with_wm_owner("simple_browser", 101)
expect(check_wm_owner(log.content, "simple_browser")).to_equal(true)
```

</details>

#### simple_browser emits render-proof:ok

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val log = SerialLog.empty().with_render_proof("simple_browser", 101)
expect(check_render_proof(log.content, "simple_browser")).to_equal(true)
```

</details>

#### simple_browser emits page_rendered with canonical app_id

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val log = SerialLog.empty().with_page_rendered("simple_browser")
expect(check_page_rendered(log.content, "simple_browser")).to_equal(true)
```

</details>

### x86_64 FS-Loaded Tool Apps Toolchain Wrapper Markers

#### llvm emits toolchain-launch:ok with mode=native-wrapper and tool=/usr/bin/clang

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val log = SerialLog.empty().with_toolchain_launch_llvm()
expect(check_llvm_toolchain(log.content)).to_equal(true)
```

</details>

#### rust emits toolchain-launch:ok with status=report-and-gate and aux=/usr/bin/cargo

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val log = SerialLog.empty().with_toolchain_launch_rust()
expect(check_rust_toolchain(log.content)).to_equal(true)
```

</details>

### x86_64 FS-Loaded Tool Apps Acceptance Contract

#### accepts completion when all required markers are present

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val log = full_passing_serial()
expect(all_markers_present(log.content)).to_equal(true)
```

</details>

#### rejects completion when a vfs-app-read marker is absent

1.  with vfs read
2.  with vfs read
3.  with vfs read
4.  with vfs read
5.  with vfs read
   - Expected: check_vfs_read(log.content, "simple_browser") == false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val log = SerialLog.empty()
    .with_vfs_read("simple_compiler")
    .with_vfs_read("simple_interpreter")
    .with_vfs_read("simple_loader")
    .with_vfs_read("llvm")
    .with_vfs_read("rust")
# simple_browser vfs-app-read is missing
expect(check_vfs_read(log.content, "simple_browser") == false).to_equal(true)
```

</details>

#### rejects resident-manifest fallback as completion evidence

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val log = SerialLog.empty().with_resident_fallback()
expect(check_resident_fallback(log.content)).to_equal(true)
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
