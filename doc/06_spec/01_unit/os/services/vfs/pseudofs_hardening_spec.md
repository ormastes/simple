# Pseudo-filesystem hardening — hostile paths / read-only enforcement (Lane HARDEN-ROBUST)

> Drives the /dev (devfs) and /proc (procfs) `Filesystem` trait adapters with

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 21 | 21 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Pseudo-filesystem hardening — hostile paths / read-only enforcement (Lane HARDEN-ROBUST)

Drives the /dev (devfs) and /proc (procfs) `Filesystem` trait adapters with

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/services/vfs/pseudofs_hardening_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Drives the /dev (devfs) and /proc (procfs) `Filesystem` trait adapters with
unknown, malformed, oversized and read-only-violating requests and asserts
each one fails closed with a clean `Result.Err` — never a crash, never an
out-of-bounds handle read, never a silent write-accept on a read-only node.
Complements the happy-path + basic fail-closed coverage in
pseudofs_mount_spec.spl.

## Scenarios

### devfs hostile input: fail closed

#### open of an unknown device is ENOENT

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- open of an unknown device is ENOENT


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("open of an unknown device is ENOENT")
var fs = DevFs.new()
assert_true(fs.open("/dev/nosuch", FileFlags.read_only()).is_err())
```

</details>

#### open of a nested path under a device is rejected

- open of a nested path under a device is rejected


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("open of a nested path under a device is rejected")
var fs = DevFs.new()
assert_true(fs.open("/dev/null/extra", FileFlags.read_only()).is_err())
```

</details>

#### open of a traversal-style /dev path is rejected

- open of a traversal-style /dev path is rejected


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("open of a traversal-style /dev path is rejected")
var fs = DevFs.new()
assert_true(fs.open("/dev/../etc/passwd", FileFlags.read_only()).is_err())
```

</details>

#### open of an absurdly long device name is rejected, not OOB

- open of an absurdly long device name is rejected, not OOB


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("open of an absurdly long device name is rejected, not OOB")
var fs = DevFs.new()
assert_true(fs.open("/dev/" + _long(4096), FileFlags.read_only()).is_err())
```

</details>

#### read from a bogus handle is EBADF (no OOB handle read)

- read from a bogus handle is EBADF (no OOB handle read)


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("read from a bogus handle is EBADF (no OOB handle read)")
var fs = DevFs.new()
assert_true(fs.read(999 as u64, 16 as u64).is_err())
```

</details>

#### write to a bogus handle is EBADF

- write to a bogus handle is EBADF


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("write to a bogus handle is EBADF")
var fs = DevFs.new()
assert_true(fs.write(999 as u64, "x".bytes()).is_err())
```

</details>

#### close of a bogus handle is EBADF

- close of a bogus handle is EBADF


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("close of a bogus handle is EBADF")
var fs = DevFs.new()
assert_true(fs.close(999 as u64).is_err())
```

</details>

#### write to read-only /dev/urandom is rejected

- write to read-only /dev/urandom is rejected


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("write to read-only /dev/urandom is rejected")
var fs = DevFs.new()
val h = fs.open("/dev/urandom", FileFlags.read_only()).unwrap()
assert_true(fs.write(h, "x".bytes()).is_err())
```

</details>

#### seek on any /dev handle is ESPIPE (not seekable)

- seek on any /dev handle is ESPIPE (not seekable)


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("seek on any /dev handle is ESPIPE (not seekable)")
var fs = DevFs.new()
val h = fs.open("/dev/zero", FileFlags.read_only()).unwrap()
assert_true(fs.seek(h, 0i64, SeekWhence.Set).is_err())
```

</details>

#### readdir of a device node (non-directory) is ENOTDIR

- readdir of a device node (non-directory) is ENOTDIR


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("readdir of a device node (non-directory) is ENOTDIR")
var fs = DevFs.new()
assert_true(fs.readdir("/dev/null").is_err())
```

</details>

#### every mutating op on /dev fails closed (EROFS)

- every mutating op on /dev fails closed (EROFS)


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("every mutating op on /dev fails closed (EROFS)")
var fs = DevFs.new()
assert_true(fs.mkdir("/dev/foo").is_err())
assert_true(fs.rmdir("/dev/foo").is_err())
assert_true(fs.unlink("/dev/null").is_err())
assert_true(fs.rename("/dev/null", "/dev/x").is_err())
assert_true(fs.symlink("/dev/null", "/dev/x").is_err())
assert_true(fs.chmod("/dev/null", 0o777 as u16).is_err())
```

</details>

### procfs hostile input: read-only + bogus pids

#### opening /proc with write flags is EROFS

- opening /proc with write flags is EROFS


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("opening /proc with write flags is EROFS")
var fs = ProcFs.new()
assert_true(fs.open("/proc/1/status", _write_flags()).is_err())
```

</details>

#### stat of a non-existent pid is ENOENT

- stat of a non-existent pid is ENOENT


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("stat of a non-existent pid is ENOENT")
var fs = ProcFs.new()
assert_true(fs.stat("/proc/4242/status").is_err())
```

</details>

#### stat of an absurdly large pid does not crash (fail closed)

- stat of an absurdly large pid does not crash (fail closed)


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("stat of an absurdly large pid does not crash (fail closed)")
var fs = ProcFs.new()
assert_true(fs.stat("/proc/999999999999999999999/status").is_err())
```

</details>

#### a non-numeric pid segment is rejected

- a non-numeric pid segment is rejected


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("a non-numeric pid segment is rejected")
var fs = ProcFs.new()
assert_true(fs.open("/proc/notapid/status", FileFlags.read_only()).is_err())
```

</details>

#### an unknown per-pid node (not 'status') is ENOENT

- an unknown per-pid node (not 'status') is ENOENT


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("an unknown per-pid node (not 'status') is ENOENT")
var fs = ProcFs.new()
assert_true(fs.open("/proc/1/environ", FileFlags.read_only()).is_err())
```

</details>

#### a deeply nested /proc path is rejected

- a deeply nested /proc path is rejected


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("a deeply nested /proc path is rejected")
var fs = ProcFs.new()
assert_true(fs.open("/proc/1/status/extra/more", FileFlags.read_only()).is_err())
```

</details>

#### write to /proc is EROFS even with a valid handle

- write to /proc is EROFS even with a valid handle


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("write to /proc is EROFS even with a valid handle")
var fs = ProcFs.new()
val h = fs.open("/proc/1/status", FileFlags.read_only()).unwrap()
assert_true(fs.write(h, "x".bytes()).is_err())
```

</details>

#### read from a bogus /proc handle is EBADF

- read from a bogus /proc handle is EBADF


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("read from a bogus /proc handle is EBADF")
var fs = ProcFs.new()
assert_true(fs.read(999 as u64, 64 as u64).is_err())
```

</details>

#### readdir of a /proc file node (non-directory) is ENOTDIR

- readdir of a /proc file node (non-directory) is ENOTDIR


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("readdir of a /proc file node (non-directory) is ENOTDIR")
var fs = ProcFs.new()
assert_true(fs.readdir("/proc/1/status").is_err())
```

</details>

#### every mutating op on /proc fails closed (EROFS)

- every mutating op on /proc fails closed (EROFS)


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("every mutating op on /proc fails closed (EROFS)")
var fs = ProcFs.new()
assert_true(fs.mkdir("/proc/x").is_err())
assert_true(fs.rmdir("/proc/1").is_err())
assert_true(fs.unlink("/proc/1/status").is_err())
assert_true(fs.rename("/proc/1", "/proc/2").is_err())
assert_true(fs.symlink("/proc/1", "/proc/2").is_err())
assert_true(fs.chmod("/proc/1/status", 0o777 as u16).is_err())
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 21 |
| Active scenarios | 21 |
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

- Canonical SPipe generation for source `d4d6bea92cfab1052a9bcb8d4f5c18baabddd7c28e5d6f8ffb83d93c24bde816`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `d4d6bea92cfab1052a9bcb8d4f5c18baabddd7c28e5d6f8ffb83d93c24bde816`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `d4d6bea92cfab1052a9bcb8d4f5c18baabddd7c28e5d6f8ffb83d93c24bde816`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/os/services/vfs/pseudofs_hardening_spec.spl
mirror: doc/06_spec/01_unit/os/services/vfs/pseudofs_hardening_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/os/services/vfs/pseudofs_hardening_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/os/services/vfs/pseudofs_hardening_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/os/services/vfs/pseudofs_hardening_spec.spl:39:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'open of an unknown device is ENOENT' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/services/vfs/pseudofs_hardening_spec.spl:45:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'open of a nested path under a device is rejected' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/services/vfs/pseudofs_hardening_spec.spl:51:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'open of a traversal-style /dev path is rejected' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
