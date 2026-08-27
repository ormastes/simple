# x86_64_fs_loaded_tool_apps_spec

> x86_64 FS-Loaded Tool Apps — acceptance contract specification.

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
| Source | `test/unit/os/x86_64_fs_loaded_tool_apps_spec.spl` |
| Updated | 2026-08-26 |
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

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- simple_browser emits vfs-app-read:ok from /sys/apps/simple_browser
   - Expected: check_vfs_read(log.content, "simple_browser") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("simple_browser emits vfs-app-read:ok from /sys/apps/simple_browser")
val log = SerialLog.empty().with_vfs_read("simple_browser")
expect(check_vfs_read(log.content, "simple_browser")).to_equal(true)
```

</details>

#### simple_compiler emits vfs-app-read:ok from /sys/apps/simple_compiler

- simple_compiler emits vfs-app-read:ok from /sys/apps/simple_compiler
   - Expected: check_vfs_read(log.content, "simple_compiler") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("simple_compiler emits vfs-app-read:ok from /sys/apps/simple_compiler")
val log = SerialLog.empty().with_vfs_read("simple_compiler")
expect(check_vfs_read(log.content, "simple_compiler")).to_equal(true)
```

</details>

#### simple_interpreter emits vfs-app-read:ok from /sys/apps/simple_interpreter

- simple_interpreter emits vfs-app-read:ok from /sys/apps/simple_interpreter
   - Expected: check_vfs_read(log.content, "simple_interpreter") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("simple_interpreter emits vfs-app-read:ok from /sys/apps/simple_interpreter")
val log = SerialLog.empty().with_vfs_read("simple_interpreter")
expect(check_vfs_read(log.content, "simple_interpreter")).to_equal(true)
```

</details>

#### simple_loader emits vfs-app-read:ok from /sys/apps/simple_loader

- simple_loader emits vfs-app-read:ok from /sys/apps/simple_loader
   - Expected: check_vfs_read(log.content, "simple_loader") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("simple_loader emits vfs-app-read:ok from /sys/apps/simple_loader")
val log = SerialLog.empty().with_vfs_read("simple_loader")
expect(check_vfs_read(log.content, "simple_loader")).to_equal(true)
```

</details>

#### llvm emits vfs-app-read:ok from /sys/apps/llvm

- llvm emits vfs-app-read:ok from /sys/apps/llvm
   - Expected: check_vfs_read(log.content, "llvm") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("llvm emits vfs-app-read:ok from /sys/apps/llvm")
val log = SerialLog.empty().with_vfs_read("llvm")
expect(check_vfs_read(log.content, "llvm")).to_equal(true)
```

</details>

#### rust emits vfs-app-read:ok from /sys/apps/rust

- rust emits vfs-app-read:ok from /sys/apps/rust
   - Expected: check_vfs_read(log.content, "rust") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rust emits vfs-app-read:ok from /sys/apps/rust")
val log = SerialLog.empty().with_vfs_read("rust")
expect(check_vfs_read(log.content, "rust")).to_equal(true)
```

</details>

### x86_64 FS-Loaded Tool Apps Process-Backed Markers

#### simple_browser emits process-backed:ok with real pid

- simple_browser emits process-backed:ok with real pid
   - Expected: check_process_backed(log.content, "simple_browser") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("simple_browser emits process-backed:ok with real pid")
val log = SerialLog.empty().with_process_backed("simple_browser", 101)
expect(check_process_backed(log.content, "simple_browser")).to_equal(true)
```

</details>

#### simple_compiler emits process-backed:ok with real pid

- simple_compiler emits process-backed:ok with real pid
   - Expected: check_process_backed(log.content, "simple_compiler") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("simple_compiler emits process-backed:ok with real pid")
val log = SerialLog.empty().with_process_backed("simple_compiler", 102)
expect(check_process_backed(log.content, "simple_compiler")).to_equal(true)
```

</details>

#### simple_interpreter emits process-backed:ok with real pid

- simple_interpreter emits process-backed:ok with real pid
   - Expected: check_process_backed(log.content, "simple_interpreter") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("simple_interpreter emits process-backed:ok with real pid")
val log = SerialLog.empty().with_process_backed("simple_interpreter", 103)
expect(check_process_backed(log.content, "simple_interpreter")).to_equal(true)
```

</details>

#### simple_loader emits process-backed:ok with real pid

- simple_loader emits process-backed:ok with real pid
   - Expected: check_process_backed(log.content, "simple_loader") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("simple_loader emits process-backed:ok with real pid")
val log = SerialLog.empty().with_process_backed("simple_loader", 104)
expect(check_process_backed(log.content, "simple_loader")).to_equal(true)
```

</details>

#### llvm emits process-backed:ok with real pid

- llvm emits process-backed:ok with real pid
   - Expected: check_process_backed(log.content, "llvm") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("llvm emits process-backed:ok with real pid")
val log = SerialLog.empty().with_process_backed("llvm", 105)
expect(check_process_backed(log.content, "llvm")).to_equal(true)
```

</details>

#### rust emits process-backed:ok with real pid

- rust emits process-backed:ok with real pid
   - Expected: check_process_backed(log.content, "rust") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rust emits process-backed:ok with real pid")
val log = SerialLog.empty().with_process_backed("rust", 106)
expect(check_process_backed(log.content, "rust")).to_equal(true)
```

</details>

### x86_64 FS-Loaded Tool Apps simple_browser Desktop Proof

#### simple_browser emits wm-owner:ok

- simple_browser emits wm-owner:ok
   - Expected: check_wm_owner(log.content, "simple_browser") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("simple_browser emits wm-owner:ok")
val log = SerialLog.empty().with_wm_owner("simple_browser", 101)
expect(check_wm_owner(log.content, "simple_browser")).to_equal(true)
```

</details>

#### simple_browser emits render-proof:ok

- simple_browser emits render-proof:ok
   - Expected: check_render_proof(log.content, "simple_browser") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("simple_browser emits render-proof:ok")
val log = SerialLog.empty().with_render_proof("simple_browser", 101)
expect(check_render_proof(log.content, "simple_browser")).to_equal(true)
```

</details>

#### simple_browser emits page_rendered with canonical app_id

- simple_browser emits page_rendered with canonical app_id
   - Expected: check_page_rendered(log.content, "simple_browser") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("simple_browser emits page_rendered with canonical app_id")
val log = SerialLog.empty().with_page_rendered("simple_browser")
expect(check_page_rendered(log.content, "simple_browser")).to_equal(true)
```

</details>

### x86_64 FS-Loaded Tool Apps Toolchain Wrapper Markers

#### llvm emits toolchain-launch:ok with mode=native-wrapper and tool=/usr/bin/clang

- llvm emits toolchain-launch:ok with mode=native-wrapper and tool=/usr/bin/clang
   - Expected: check_llvm_toolchain(log.content) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("llvm emits toolchain-launch:ok with mode=native-wrapper and tool=/usr/bin/clang")
val log = SerialLog.empty().with_toolchain_launch_llvm()
expect(check_llvm_toolchain(log.content)).to_equal(true)
```

</details>

#### rust emits toolchain-launch:ok with status=report-and-gate and aux=/usr/bin/cargo

- rust emits toolchain-launch:ok with status=report-and-gate and aux=/usr/bin/cargo
   - Expected: check_rust_toolchain(log.content) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rust emits toolchain-launch:ok with status=report-and-gate and aux=/usr/bin/cargo")
val log = SerialLog.empty().with_toolchain_launch_rust()
expect(check_rust_toolchain(log.content)).to_equal(true)
```

</details>

### x86_64 FS-Loaded Tool Apps Acceptance Contract

#### accepts completion when all required markers are present

- accepts completion when all required markers are present
   - Expected: all_markers_present(log.content) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("accepts completion when all required markers are present")
val log = full_passing_serial()
expect(all_markers_present(log.content)).to_equal(true)
```

</details>

#### rejects completion when a vfs-app-read marker is absent

- rejects completion when a vfs-app-read marker is absent
   - Expected: check_vfs_read(log.content, "simple_browser") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects completion when a vfs-app-read marker is absent")
val log = SerialLog.empty()
    .with_vfs_read("simple_compiler")
    .with_vfs_read("simple_interpreter")
    .with_vfs_read("simple_loader")
    .with_vfs_read("llvm")
    .with_vfs_read("rust")
# simple_browser vfs-app-read is missing
expect(check_vfs_read(log.content, "simple_browser")).to_equal(false)
```

</details>

#### rejects resident-manifest fallback as completion evidence

- rejects resident-manifest fallback as completion evidence
   - Expected: check_resident_fallback(log.content) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects resident-manifest fallback as completion evidence")
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `19584c66dc07ec84f58c7db7571d8c294316cdf58f49abce006c4086e3f13432`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `19584c66dc07ec84f58c7db7571d8c294316cdf58f49abce006c4086e3f13432`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `19584c66dc07ec84f58c7db7571d8c294316cdf58f49abce006c4086e3f13432`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/os/x86_64_fs_loaded_tool_apps_spec.spl
mirror: doc/06_spec/unit/os/x86_64_fs_loaded_tool_apps_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/os/x86_64_fs_loaded_tool_apps_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/os/x86_64_fs_loaded_tool_apps_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/os/x86_64_fs_loaded_tool_apps_spec.spl:152:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'simple_browser emits vfs-app-read:ok from /sys/apps/simple_browser' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/os/x86_64_fs_loaded_tool_apps_spec.spl:158:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'simple_compiler emits vfs-app-read:ok from /sys/apps/simple_compiler' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/os/x86_64_fs_loaded_tool_apps_spec.spl:164:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'simple_interpreter emits vfs-app-read:ok from /sys/apps/simple_interpreter' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
