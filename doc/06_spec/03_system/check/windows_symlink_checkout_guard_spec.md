# Windows Symlink-Checkout Guard and Materializer

> Two artifacts guard this class of failure:

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Windows Symlink-Checkout Guard and Materializer

Two artifacts guard this class of failure:

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Requirements | N/A |
| Plan | doc/08_tracking/bug/windows_build_subcommand_silent_noop_stale_binary_2026-08-05.md |
| Design | doc/04_architecture/compiler/misc/file_class_structure.md |
| Source | `test/03_system/check/windows_symlink_checkout_guard_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Two artifacts guard this class of failure:

- `scripts/check/check-no-new-symlinks-push.shs` — a pre-push guard that
  refuses (fail-closed) an outgoing commit range that introduces a NEW
  symlink (a path that was not mode 120000 at the base and is at the tip).
  Existing symlinks already in the repo are grandfathered; only growth is
  blocked.
- `scripts/setup/materialize-symlinks-windows.shs` — replaces a degraded
  symlink placeholder (a plain text file whose content is the literal target
  string, produced by `core.symlinks=false`) with a real NTFS junction (for a
  directory target) or hard link (for a file target). Neither NTFS feature
  needs `SeCreateSymbolicLinkPrivilege`, so this works even on a restricted
  session. Wired into `scripts/bootstrap/bootstrap-windows.sh` so every
  Windows bootstrap runs it automatically before the rest of the pipeline.

## Requirements

**Requirements:** N/A

- REQ-WIN-SYMLINK-001: The push guard's embedded selftest passes on its own
  synthetic fixtures.
- REQ-WIN-SYMLINK-002: The push guard detects a genuinely new symlink
  introduced between two real commits and refuses (exit 1).
- REQ-WIN-SYMLINK-003: The push guard passes (exit 0) a range that touches no
  symlinks, and passes a range that only retargets an EXISTING symlink.
- REQ-WIN-SYMLINK-004: The materializer replaces a directory-target
  placeholder with a working junction and a file-target placeholder with a
  working hard link, and is idempotent on a second run.

## Plan

**Plan:** doc/08_tracking/bug/windows_build_subcommand_silent_noop_stale_binary_2026-08-05.md

1. Run the guard's `--selftest` and confirm it reports its fixtures correct.
2. Build a throwaway git repo, add a new symlink, confirm the guard flags it.
3. Build a throwaway git repo with no symlink growth, confirm the guard
   passes; also confirm retargeting an existing symlink still passes.
4. Build a throwaway git repo containing a directory-target and a
   file-target symlink, check it out with `core.symlinks=false` so both
   degrade to placeholders, run the materializer, and confirm both resolve
   for real — then run it again and confirm nothing changes (idempotent).

## Design

**Design:** doc/04_architecture/compiler/misc/file_class_structure.md

Both scripts are POSIX `sh`, invoked as external processes via
`process_run`, exactly like every other `scripts/check/*.shs` contract spec
in this directory — this spec asserts on real process exit codes and real
stdout, not on source text alone.

## Examples

```sh
bin/simple test test/03_system/check/windows_symlink_checkout_guard_spec.spl --clean
```

## Scenarios

### check-no-new-symlinks-push guard

#### passes its own embedded selftest

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- passes its own embedded selftest
   - Expected: code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("passes its own embedded selftest")
val (stdout, _stderr, code) = process_run("sh", ["scripts/check/check-no-new-symlinks-push.shs", "--selftest"])
expect(code).to_equal(0)
expect(stdout).to_contain("selftest 4/4 fixtures correct")
```

</details>

#### refuses a range that introduces a brand-new symlink

- refuses a range that introduces a brand-new symlink
   - Expected: code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("refuses a range that introduces a brand-new symlink")
val root = "build/test-no-new-symlinks-guard-added"
val command = "rm -rf " + root + " && mkdir -p " + root + " && cd " + root + " && " +
    "git init -q && " +
    "git config user.email t@example.com && " +
    "git config user.name t && " +
    "printf 'hello\\n' > keep.txt && " +
    "git add keep.txt && " +
    "git commit -q -m base && " +
    "BASE=$(git rev-parse HEAD) && " +
    "printf '../elsewhere' > new_link && " +
    "git update-index --add --cacheinfo 120000,$(git hash-object -w new_link),new_link && " +
    "git commit -q -m 'adds symlink' && " +
    "TIP=$(git rev-parse HEAD) && " +
    "sh ../../scripts/check/check-no-new-symlinks-push.shs \"$BASE..$TIP\" > out.txt 2>&1; echo \"EXIT=$?\" >> out.txt"
val (_stdout, _stderr, code) = process_run("sh", ["-c", command])
expect(code).to_equal(0)

val output = file_read(root + "/out.txt")
expect(output).to_contain("EXIT=1")
expect(output).to_contain("NEW SYMLINK(S) INTRODUCED")
expect(output).to_contain("new_link")
expect(output).to_contain("check-no-new-symlinks-push: FAIL")
```

</details>

#### passes a range with no symlink growth, including a retargeted existing symlink

- passes a range with no symlink growth, including a retargeted existing symlink
   - Expected: code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 26 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("passes a range with no symlink growth, including a retargeted existing symlink")
val root = "build/test-no-new-symlinks-guard-clean"
val command = "rm -rf " + root + " && mkdir -p " + root + " && cd " + root + " && " +
    "git init -q && " +
    "git config user.email t@example.com && " +
    "git config user.name t && " +
    "printf 'hello\\n' > keep.txt && " +
    "printf '../a' > existing_link && " +
    "git add keep.txt && " +
    "git update-index --add --cacheinfo 120000,$(git hash-object -w existing_link),existing_link && " +
    "git commit -q -m base && " +
    "BASE=$(git rev-parse HEAD) && " +
    "printf 'hello again\\n' > keep.txt && " +
    "printf '../b' > existing_link && " +
    "git update-index --add --cacheinfo 120000,$(git hash-object -w existing_link),existing_link && " +
    "git add keep.txt && " +
    "git commit -q -m 'edit + retarget existing symlink' && " +
    "TIP=$(git rev-parse HEAD) && " +
    "sh ../../scripts/check/check-no-new-symlinks-push.shs \"$BASE..$TIP\" > out.txt 2>&1; echo \"EXIT=$?\" >> out.txt"
val (_stdout, _stderr, code) = process_run("sh", ["-c", command])
expect(code).to_equal(0)

val output = file_read(root + "/out.txt")
expect(output).to_contain("EXIT=0")
expect(output).to_contain("check-no-new-symlinks-push: PASS")
```

</details>

### materialize-symlinks-windows script

#### is scoped to Windows/MSYS hosts and no-ops cleanly elsewhere

- is scoped to Windows/MSYS hosts and no-ops cleanly elsewhere


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("is scoped to Windows/MSYS hosts and no-ops cleanly elsewhere")
val script = file_read("scripts/setup/materialize-symlinks-windows.shs")
expect(script).to_contain("MINGW*|MSYS*|CYGWIN*")
expect(script).to_contain("this script is Windows-only")
expect(script).to_contain("New-Item -ItemType Junction")
expect(script).to_contain("New-Item -ItemType HardLink")
expect(script).to_contain("SeCreateSymbolicLinkPrivilege")
```

</details>

#### resolves a directory-target and a file-target placeholder, and is idempotent

- resolves a directory-target and a file-target placeholder, and is idempotent
   - Expected: code equals `0`
- Non-Windows hosts report the scoped no-op and skip the rest of this check
- Windows hosts must resolve both placeholders and be idempotent on rerun
   - Expected: inner equals `x`
   - Expected: fcontent equals `y`


<details>
<summary>Executable SSpec</summary>

Runnable source: 41 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("resolves a directory-target and a file-target placeholder, and is idempotent")
val root = "build/test-materialize-symlinks-windows"
val command = "rm -rf " + root + " && mkdir -p " + root + "/src && cd " + root + " && " +
    "git init -q && " +
    "git config user.email t@example.com && " +
    "git config user.name t && " +
    "git config core.symlinks false && " +
    "mkdir -p src/real_dir && printf 'x' > src/real_dir/inner.txt && " +
    "printf 'y' > src/real_file.txt && " +
    "git add -A && git commit -q -m base && " +
    "printf 'real_dir' > src/dir_link && " +
    "printf 'real_file.txt' > src/file_link && " +
    "git update-index --add --cacheinfo 120000,$(git hash-object -w src/dir_link),src/dir_link && " +
    "git update-index --add --cacheinfo 120000,$(git hash-object -w src/file_link),src/file_link && " +
    "git commit -q -m 'add symlinks' && " +
    "git checkout -q -- . && " +
    "cd - >/dev/null && " +
    "sh scripts/setup/materialize-symlinks-windows.shs " + root + " > " + root + "/run1.txt 2>&1 && " +
    "sh scripts/setup/materialize-symlinks-windows.shs " + root + " > " + root + "/run2.txt 2>&1"
val (_stdout, _stderr, code) = process_run("sh", ["-c", command])
expect(code).to_equal(0)

val run1 = file_read(root + "/run1.txt")
val run2 = file_read(root + "/run2.txt")

step("Non-Windows hosts report the scoped no-op and skip the rest of this check")
if run1.contains("Windows-only"):
    expect(run1).to_contain("materialize-symlinks-windows: this script is Windows-only")
else:
    step("Windows hosts must resolve both placeholders and be idempotent on rerun")
    expect(run1).to_contain("created=2")
    expect(run1).to_contain("failed=0")
    expect(run2).to_contain("created=0")
    expect(run2).to_contain("already_ok=2")
    expect(run2).to_contain("failed=0")

    val inner = file_read(root + "/src/dir_link/inner.txt")
    expect(inner).to_equal("x")
    val fcontent = file_read(root + "/src/file_link")
    expect(fcontent).to_equal("y")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Plan:** `doc/08_tracking/bug/windows_build_subcommand_silent_noop_stale_binary_2026-08-05.md`
- **Design:** `doc/04_architecture/compiler/misc/file_class_structure.md`


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
- `REQ-WIN-SYMLINK-001:`
- `REQ-WIN-SYMLINK-002:`
- `REQ-WIN-SYMLINK-003:`
- `REQ-WIN-SYMLINK-004:`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `2e359226528ae65fdc2800955f6b23f580ab1d7cfa6030eafaf728642284c761`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `2e359226528ae65fdc2800955f6b23f580ab1d7cfa6030eafaf728642284c761`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `2e359226528ae65fdc2800955f6b23f580ab1d7cfa6030eafaf728642284c761`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/03_system/check/windows_symlink_checkout_guard_spec.spl
mirror: doc/06_spec/03_system/check/windows_symlink_checkout_guard_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/check/windows_symlink_checkout_guard_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/check/windows_symlink_checkout_guard_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/check/windows_symlink_checkout_guard_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 4 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/check/windows_symlink_checkout_guard_spec.spl:89:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'passes its own embedded selftest' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/check/windows_symlink_checkout_guard_spec.spl:96:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'refuses a range that introduces a brand-new symlink' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/check/windows_symlink_checkout_guard_spec.spl:122:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'passes a range with no symlink growth, including a retargeted existing symlink' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
