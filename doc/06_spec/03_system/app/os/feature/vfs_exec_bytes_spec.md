# VFS Exec Byte Buffer Spec

> Verifies that boot-file bytes returned through the VFS exec path are cloned

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# VFS Exec Byte Buffer Spec

Verifies that boot-file bytes returned through the VFS exec path are cloned

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/03_system/app/os/feature/vfs_exec_bytes_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Verifies that boot-file bytes returned through the VFS exec path are cloned
before they are cached or handed to callers.

## Scenarios

### vfs_exec_bytes feature spec

#### clones FAT32 byte buffers instead of sharing array storage

- clones FAT32 byte buffers instead of sharing array storage
   - Expected: cloned equals `[0x41u8, 0x42u8, 0x43u8]`
   - Expected: source equals `[0x41u8, 0x42u8, 0x43u8, 0x44u8]`
   - Expected: cloned equals `[0x41u8, 0x42u8, 0x43u8]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("clones FAT32 byte buffers instead of sharing array storage")
var source = [0x41u8, 0x42u8, 0x43u8]
val cloned = _clone_bytes(source)

expect(cloned).to_equal([0x41u8, 0x42u8, 0x43u8])

source.push(0x44u8)

expect(source).to_equal([0x41u8, 0x42u8, 0x43u8, 0x44u8])
expect(cloned).to_equal([0x41u8, 0x42u8, 0x43u8])
```

</details>

#### maps canonical filesystem app SMF paths to FAT32 8.3 disk files

- maps canonical filesystem app SMF paths to FAT32 8.3 disk files
   - Expected: _vfs_exec_disk_alias("/sys/apps/browser_demo.smf") equals `/SYS/APPS/BROWSMF.SMF`
   - Expected: _vfs_exec_disk_alias("/sys/apps/file_manager.smf") equals `/SYS/APPS/FILESMF.SMF`
   - Expected: _vfs_exec_disk_alias("/sys/apps/hello_world.smf") equals `/SYS/APPS/HELLOSMF.SMF`
   - Expected: _vfs_exec_disk_alias("/sys/apps/shell.smf") equals `/SYS/APPS/SHELLSMF.SMF`
   - Expected: _vfs_exec_disk_alias("/sys/apps/editor.smf") equals `/SYS/APPS/EDITORSM.SMF`
   - Expected: _vfs_exec_disk_alias("/tmp/notes.txt") equals `/tmp/notes.txt`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("maps canonical filesystem app SMF paths to FAT32 8.3 disk files")
app_registry_load_hardcoded_fallback()
expect(_vfs_exec_disk_alias("/sys/apps/browser_demo.smf")).to_equal("/SYS/APPS/BROWSMF.SMF")
expect(_vfs_exec_disk_alias("/sys/apps/file_manager.smf")).to_equal("/SYS/APPS/FILESMF.SMF")
expect(_vfs_exec_disk_alias("/sys/apps/hello_world.smf")).to_equal("/SYS/APPS/HELLOSMF.SMF")
expect(_vfs_exec_disk_alias("/sys/apps/shell.smf")).to_equal("/SYS/APPS/SHELLSMF.SMF")
expect(_vfs_exec_disk_alias("/sys/apps/editor.smf")).to_equal("/SYS/APPS/EDITORSM.SMF")
expect(_vfs_exec_disk_alias("/tmp/notes.txt")).to_equal("/tmp/notes.txt")
```

</details>

#### maps shell-style executable paths to shared SMF app aliases

- maps shell-style executable paths to shared SMF app aliases
   - Expected: _vfs_exec_disk_alias("/bin/simple") equals `/SYS/APPS/SIMPLSTC.SMF`
   - Expected: _vfs_exec_disk_alias("/usr/bin/simple") equals `/SYS/APPS/SIMPLSTC.SMF`
   - Expected: _vfs_exec_disk_alias("/bin/sh") equals `/SYS/APPS/SHELLSMF.SMF`
   - Expected: _vfs_exec_disk_alias("/usr/bin/shell") equals `/SYS/APPS/SHELLSMF.SMF`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("maps shell-style executable paths to shared SMF app aliases")
app_registry_load_hardcoded_fallback()
expect(_vfs_exec_disk_alias("/bin/simple")).to_equal("/SYS/APPS/SIMPLSTC.SMF")
expect(_vfs_exec_disk_alias("/usr/bin/simple")).to_equal("/SYS/APPS/SIMPLSTC.SMF")
expect(_vfs_exec_disk_alias("/bin/sh")).to_equal("/SYS/APPS/SHELLSMF.SMF")
expect(_vfs_exec_disk_alias("/usr/bin/shell")).to_equal("/SYS/APPS/SHELLSMF.SMF")
```

</details>

#### keeps NVFS path reads pure Simple through the native driver

- keeps NVFS path reads pure Simple through the native driver
   - Expected: d.mount(MountOptions.default()).is_ok() is true
   - Expected: d.write(fh, 0, payload).unwrap() equals `5`
   - Expected: d.stat(path).unwrap().size equals `5u64`
   - Expected: d.read(rh, 0, out).unwrap() equals `5`
   - Expected: out equals `payload`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("keeps NVFS path reads pure Simple through the native driver")
var d = NvfsDriver.new("vfs-exec-nvfs")
expect(d.mount(MountOptions.default()).is_ok()).to_equal(true)
val path = Path(raw: "/SYS/VERSION.TXT")
val fh = d.open(path, OpenFlags.read_write().with_create()).unwrap()
val payload: [u8] = [0x30u8, 0x2Eu8, 0x31u8, 0x2Eu8, 0x30u8]
expect(d.write(fh, 0, payload).unwrap()).to_equal(5)
d.close(fh)

expect(d.stat(path).unwrap().size).to_equal(5u64)
val rh = d.open(path, OpenFlags.read_only()).unwrap()
var out: [u8] = [0u8, 0u8, 0u8, 0u8, 0u8]
expect(d.read(rh, 0, out).unwrap()).to_equal(5)
d.close(rh)
expect(out).to_equal(payload)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `b08902ed9666c360abfbfdeccc08203b2ec513c30612e8d7581cdc56de55edf6`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `b08902ed9666c360abfbfdeccc08203b2ec513c30612e8d7581cdc56de55edf6`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `b08902ed9666c360abfbfdeccc08203b2ec513c30612e8d7581cdc56de55edf6`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/03_system/app/os/feature/vfs_exec_bytes_spec.spl
mirror: doc/06_spec/03_system/app/os/feature/vfs_exec_bytes_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/app/os/feature/vfs_exec_bytes_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/app/os/feature/vfs_exec_bytes_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/app/os/feature/vfs_exec_bytes_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/app/os/feature/vfs_exec_bytes_spec.spl:23:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'clones FAT32 byte buffers instead of sharing array storage' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/app/os/feature/vfs_exec_bytes_spec.spl:36:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'maps canonical filesystem app SMF paths to FAT32 8.3 disk files' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/app/os/feature/vfs_exec_bytes_spec.spl:47:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'maps shell-style executable paths to shared SMF app aliases' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
