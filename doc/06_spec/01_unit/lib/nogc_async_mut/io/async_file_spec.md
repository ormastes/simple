# Async File Specification

> Tests covering async file — errno translation, async file — stat, async file — AsyncDir.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 14 | 14 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Async File Specification

## Scenarios

### async file — errno translation

#### maps ENOENT to NotFound

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- maps ENOENT to NotFound
   - Expected: e.kind == IoErrorKind.NotFound is true
   - Expected: e.message equals `file not found`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("maps ENOENT to NotFound")
val e = errno_to_io_error(0 - 2)
expect(e.kind == IoErrorKind.NotFound).to_equal(true)
expect(e.message).to_equal("file not found")
```

</details>

#### maps EACCES to PermissionDenied

- maps EACCES to PermissionDenied
   - Expected: e.kind == IoErrorKind.PermissionDenied is true
   - Expected: e.message equals `permission denied`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("maps EACCES to PermissionDenied")
val e = errno_to_io_error(0 - 13)
expect(e.kind == IoErrorKind.PermissionDenied).to_equal(true)
expect(e.message).to_equal("permission denied")
```

</details>

#### maps EEXIST to AlreadyExists

- maps EEXIST to AlreadyExists
   - Expected: e.kind == IoErrorKind.AlreadyExists is true
   - Expected: e.message equals `already exists`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("maps EEXIST to AlreadyExists")
val e = errno_to_io_error(0 - 17)
expect(e.kind == IoErrorKind.AlreadyExists).to_equal(true)
expect(e.message).to_equal("already exists")
```

</details>

#### maps EISDIR to InvalidInput

- maps EISDIR to InvalidInput
   - Expected: e.kind == IoErrorKind.InvalidInput is true
   - Expected: e.message equals `is a directory`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("maps EISDIR to InvalidInput")
val e = errno_to_io_error(0 - 21)
expect(e.kind == IoErrorKind.InvalidInput).to_equal(true)
expect(e.message).to_equal("is a directory")
```

</details>

#### maps ENOSPC to Other with a no-space message

- maps ENOSPC to Other with a no-space message
   - Expected: e.kind == IoErrorKind.Other is true
   - Expected: e.message equals `no space left on device`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("maps ENOSPC to Other with a no-space message")
val e = errno_to_io_error(0 - 28)
expect(e.kind == IoErrorKind.Other).to_equal(true)
expect(e.message).to_equal("no space left on device")
```

</details>

#### falls back to Other for an unrecognised errno

- falls back to Other for an unrecognised errno
   - Expected: e.kind == IoErrorKind.Other is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("falls back to Other for an unrecognised errno")
val e = errno_to_io_error(0 - 99)
expect(e.kind == IoErrorKind.Other).to_equal(true)
```

</details>

#### distinguishes the mapped kinds from one another

- distinguishes the mapped kinds from one another
   - Expected: not_found.kind == denied.kind is false
   - Expected: denied.kind == exists.kind is false
   - Expected: not_found.kind == exists.kind is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("distinguishes the mapped kinds from one another")
val not_found = errno_to_io_error(0 - 2)
val denied = errno_to_io_error(0 - 13)
val exists = errno_to_io_error(0 - 17)
expect(not_found.kind == denied.kind).to_equal(false)
expect(denied.kind == exists.kind).to_equal(false)
expect(not_found.kind == exists.kind).to_equal(false)
```

</details>

### async file — stat

#### fails on a path that does not exist

- fails on a path that does not exist
   - Expected: r.is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("fails on a path that does not exist")
val r = stat("/nonexistent/definitely/missing/path")
expect(r.is_err()).to_equal(true)
```

</details>

#### succeeds on an existing directory

- succeeds on an existing directory
   - Expected: r.is_ok() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("succeeds on an existing directory")
val r = stat("/tmp")
expect(r.is_ok()).to_equal(true)
```

</details>

#### reports a directory as a directory and not a file

- reports a directory as a directory and not a file
   - Expected: r.is_ok() is true
   - Expected: st.is_dir is true
   - Expected: st.is_file is false
   - Expected: "stat /tmp failed" equals `stat /tmp to succeed`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reports a directory as a directory and not a file")
val r = stat("/tmp")
expect(r.is_ok()).to_equal(true)
match r:
    case Ok(st):
        expect(st.is_dir).to_equal(true)
        expect(st.is_file).to_equal(false)
    case Err(e):
        expect("stat /tmp failed").to_equal("stat /tmp to succeed")
```

</details>

### async file — AsyncDir

#### lists an existing directory

- lists an existing directory
   - Expected: r.is_ok() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("lists an existing directory")
val r = AsyncDir.readdir("/tmp")
expect(r.is_ok()).to_equal(true)
```

</details>

#### fails to list a directory that does not exist

- fails to list a directory that does not exist
   - Expected: r.is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("fails to list a directory that does not exist")
val r = AsyncDir.readdir("/nonexistent/definitely/missing/dir")
expect(r.is_err()).to_equal(true)
```

</details>

#### creates a directory, sees it in the listing, then removes it

- creates a directory, sees it in the listing, then removes it
   - Expected: made.is_ok() is true
   - Expected: after_create.is_ok() is true
   - Expected: removed.is_ok() is true
   - Expected: after_remove.is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates a directory, sees it in the listing, then removes it")
val path = "/tmp/vaclane_async_file_spec_dir"
val made = AsyncDir.mkdir(path, 493)
expect(made.is_ok()).to_equal(true)
val after_create = stat(path)
expect(after_create.is_ok()).to_equal(true)
val removed = AsyncDir.remove(path)
expect(removed.is_ok()).to_equal(true)
val after_remove = stat(path)
expect(after_remove.is_err()).to_equal(true)
```

</details>

#### reports a newly created directory as a directory

- reports a newly created directory as a directory
   - Expected: made.is_ok() is true
   - Expected: info.is_dir is true
   - Expected: "stat of created dir failed" equals `it to succeed`
   - Expected: removed.is_ok() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reports a newly created directory as a directory")
val path = "/tmp/vaclane_async_file_spec_dir2"
val made = AsyncDir.mkdir(path, 493)
expect(made.is_ok()).to_equal(true)
val st = stat(path)
match st:
    case Ok(info):
        expect(info.is_dir).to_equal(true)
    case Err(e):
        expect("stat of created dir failed").to_equal("it to succeed")
val removed = AsyncDir.remove(path)
expect(removed.is_ok()).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/nogc_async_mut/io/async_file_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering async file — errno translation, async file — stat, async file — AsyncDir.
- async file — errno translation
- async file — stat
- async file — AsyncDir

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 14 |
| Active scenarios | 14 |
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

- Canonical SPipe generation for source `c2a99888f8f025d2b97ce117d54d317fc6f88785abad8c540c7cafb5f73fbf20`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `c2a99888f8f025d2b97ce117d54d317fc6f88785abad8c540c7cafb5f73fbf20`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `c2a99888f8f025d2b97ce117d54d317fc6f88785abad8c540c7cafb5f73fbf20`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/nogc_async_mut/io/async_file_spec.spl
mirror: doc/06_spec/01_unit/lib/nogc_async_mut/io/async_file_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/nogc_async_mut/io/async_file_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/nogc_async_mut/io/async_file_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/nogc_async_mut/io/async_file_spec.spl:31:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'maps ENOENT to NotFound' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/nogc_async_mut/io/async_file_spec.spl:38:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'maps EACCES to PermissionDenied' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/nogc_async_mut/io/async_file_spec.spl:45:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'maps EEXIST to AlreadyExists' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
