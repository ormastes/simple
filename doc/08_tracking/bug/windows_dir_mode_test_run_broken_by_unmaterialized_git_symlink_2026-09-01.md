# Windows: `simple test <directory>` fails entirely — test daemon import chain hits an unmaterialized git symlink

**Status:** FIXED 2026-09-06 — see "Fix 2026-09-06" below.
**Filed:** 2026-09-01
**Found by:** triage of `test/01_unit/lib/std/` failures on Windows.

## Symptom

```bash
B=src/compiler_rust/target/release/simple.exe
SIMPLE_BINARY="$B" "$B" test test/01_unit/lib/std/
```

fails immediately with:

```
error: compile failed: parse: in
"\\?\C:\Users\ormas\dev\simple\src\app\debug\coordinator.spl":
Unexpected token: expected expression, found Slash
```

before executing a single spec — no `Results:` line, nothing runnable.
Per-file invocation (`"$B" test <one-spec-file>`) works fine, so this only
affects directory-mode / whole-area runs.

## Root cause

`src/app/debug/coordinator.spl` is a git symlink (mode `120000`) pointing at
`../../lib/nogc_sync_mut/debug/coordinator.spl`:

```bash
git ls-files -s src/app/debug/coordinator.spl
# 120000 e7c682d2084ad51579fe4c57492492d1824cdae4 0	src/app/debug/coordinator.spl
git config core.symlinks
# false
```

With `core.symlinks=false` (the default on this Windows checkout), git
checks the symlink out as a **plain text file containing the link target
string** (`../../lib/nogc_sync_mut/debug/coordinator.spl`, 45 bytes, no
newline) instead of a real symlink or the target's content. When the test
daemon's own module graph (`src/app/test_daemon/__init__.spl` ->
... -> `src/app/debug/coordinator.spl`) is compiled as part of directory-mode
test discovery, the compiler tries to parse that 45-byte path string as
Simple source and chokes on the first `/`.

This is not specific to `test/01_unit/lib/std/` — any directory-mode test
run that pulls in the test daemon's import graph on a `core.symlinks=false`
Windows checkout hits the same wall. The repo has **91 tracked git symlinks**
total (`git ls-files -s | awk '$1==120000'`), so any other module reachable
through one of those 91 paths would fail the same way if imported.

## Why not fixed here

This is an environment/checkout configuration issue (`core.symlinks=false`),
not a defect in `test/01_unit/lib/std/` or in stdlib product code. Per
CLAUDE.md's git safety protocol, changing git config is out of scope for
this task. The workaround used for this triage pass was running every spec
file individually (`"$B" test <file>`) rather than by directory, which
avoids compiling the test daemon's broader import graph.

## Suggested fix directions (not attempted here)

- Enable `core.symlinks=true` and re-checkout on Windows dev machines (needs
  Developer Mode or admin, and a `git checkout -- .` after enabling).
- Or: have the compiler's module loader detect a checked-out git-symlink
  placeholder (small file whose entire content is a relative path with no
  Simple-syntax markers) and follow it, so the tree keeps working the same
  under both `core.symlinks` settings.
- Or: stop using git symlinks for module files reachable by the test daemon
  import graph specifically.

## Repro

```bash
B=src/compiler_rust/target/release/simple.exe
SIMPLE_BINARY="$B" "$B" test test/01_unit/lib/std/ 2>&1 | tail -5
```

---

## Fix 2026-09-06

### What the sibling fix already covered, and what it did not

`windows_git_symlinks_materialize_as_path_text_2026-09-02.md` (FIXED) wired
`scripts/setup/materialize-symlinks-windows.shs` into every worktree
`check-main-test-runnable-push.shs` creates. That closes the guard's lane. It
does **not** run on an ordinary developer checkout, and this box proved it: a
`git checkout -f --detach origin/main` on 2026-09-06 left the whole tree
degraded again.

Measured before any edit (binary `src/compiler_rust/target/release/simple.exe`,
exit status read into a variable on the line after the invocation, never
through a pipe):

```
$ ls -l src/app/debug/coordinator.spl        # 45 bytes of path text
$ simple.exe check src/app/debug/coordinator.spl ; rc=$?
rc=1   cannot resolve import `compiler.frontend.core.lexer`
       ... module path segment `compiler` not found
$ sh scripts/setup/materialize-symlinks-windows.shs ; rc=$?
materialize-symlinks-windows: created=95 already_ok=8 skipped_pending(target missing)=13 failed=0
materialize_rc=0
$ simple.exe check src/app/debug/coordinator.spl ; rc=$?
AFTER_check_rc=0   All checks passed (1 file(s))
$ wc -c src/app/debug/coordinator.spl
521
```

So the reported `found Slash` / unresolved-import wall is environment repair,
not a code defect — and it is already scripted.

### The residue this bug is really about: dir-mode under-collection

The part the materialiser cannot rescue by itself is **silent**, and it is
specific to directory mode. `git ls-files -s test | awk '$1=="120000"'` → **23**
tracked symlinks under `test/`, six of them DIRECTORY aliases inside trees that
`simple test <dir>` walks:

```
test/01_unit/app/desugar/app       test/03_system/feature/lib/app
test/01_unit/compiler/compiler     test/03_system/feature/lib/compiler
test/01_unit/compiler/std          test/03_system/feature/lib/lib
test/01_unit/lib/database/lib
```

Degraded, each stops being a directory, so `dir_walk` never descends into the
aliased subtree. The run then collects fewer specs and reports **green** — the
"a scan that found nothing may have scanned nothing" trap from
`.claude/rules/testing.md`. No guard, and none of the sibling fix's specs,
detects that.

### Fix

`src/lib/nogc_sync_mut/test_runner/test_runner_files.spl` (the live module —
`std.test_runner.test_runner_files` resolves through the
`src/lib/nogc_async_mut/test_runner/test_runner_files.spl` re-export shim to
here; `src/app/test_runner_new/test_runner_files.spl` is a stale unimported
duplicate and was deliberately left untouched):

- `is_symlink_placeholder(path)` — detector. Shape mirrors
  `placeholder_looks_like_target` in `materialize-symlinks-windows.shs` (the
  single pre-existing detector; not re-invented) and tightens it so real source
  can never match: basename is extensionless or `.spl`, content non-empty and
  `< 4096` bytes, no newline/CR/space/tab anywhere, and contains a separator.
- `symlink_placeholder_report(paths)` — pure diagnostic text, spec-pinnable.
- `discover_test_files_slow` — after `dir_walk`, refuses a tree containing any
  placeholder: prints the report and returns `[]`. Returning `[]` is the whole
  mechanism for failing closed — for an explicit path
  `test_empty_selection_is_success` is already false, so the run cannot go
  green.
- `discover_test_files_fast` — **two further changes, both found by running the
  fixture twice instead of once.** (a) The slow path's result is no longer
  cached when it refused (`save_manifest_from_discovery` is now called only for
  a non-empty result); otherwise the refusal writes a manifest built from a
  degraded tree. (b) A FRESH manifest skips the walk entirely, so the slow
  path's refusal never fires at all — the fast branch now re-checks the tree
  itself. That check passes `include_spl = false`, i.e. it reads only
  EXTENSIONLESS entries, so the fast path keeps its "no per-spec content reads"
  property; a degraded `.spl` alias is not silent anyway, the compiler rejects
  it loudly with `found Slash`. Measured before this: run 1 (fresh manifest
  from an earlier run) returned `Results: 1 total` with **no diagnostic**,
  run 2 refused — exactly the silent green the fix exists to remove.

It deliberately does **not** follow the placeholder. Unblock condition 3 of the
sibling bug ("a parse error becoming a silent path redirect is worse than the
defect") applies here unchanged.

### Verification on the real box (2026-09-06)

Fixture tree `build/lanec-dirmode/` with one spec and one directory-alias
placeholder (`compiler` → `../../src/lib/nogc_sync_mut/test_runner`):

```
=== WITH placeholder ===
rc=4
error: 1 unmaterialized git symlink(s) in the walked tree —
  placeholder: build\lanec-dirmode\compiler
  remedy: sh scripts/setup/materialize-symlinks-windows.shs
No test files found in build/lanec-dirmode/
Results: 0 total, 0 passed, 0 failed
```

Refusal is **stable across the manifest cache** — three consecutive runs of the
same invocation, which is what exposed the fast-path hole above:

```
RUN1 rc=4 1 diag  |  Results: 0 total, 0 passed, 0 failed
RUN2 rc=4 1 diag  |  Results: 0 total, 0 passed, 0 failed
RUN3 rc=4 1 diag  |  Results: 0 total, 0 passed, 0 failed
```

Contrast, same tree with the placeholder removed — also run twice, to prove the
check is not blanket-refusing and does not stick in the manifest:

```
NOPH RUN1 rc=1 unmat=0  |  Results: 1 total, 0 passed, 1 failed
NOPH RUN2 rc=1 unmat=0  |  Results: 1 total, 0 passed, 1 failed
```

No false positive on the real tree. `test/01_unit/compiler/` holds two genuine
symlinks (`compiler -> ../../../src/compiler`, `std -> ../../../src/lib`,
`lrwxrwxrwx`, intact from Jun 15 in this checkout):

```
$ SIMPLE_BINARY=$B $B test --list test/01_unit/compiler/ ; rc=$?
rc=0   unmaterialized-diagnostic count = 0
```

The "before" behaviour is the WITHOUT-placeholder run in reverse and was not
separately re-measured: prior to this change the placeholder was simply an
extensionless file that `is_test_file` rejected, so discovery ignored it, never
descended into what it aliases, and reported on whatever it did find — no
diagnostic, no distinction between "that subtree has no specs" and "that
subtree was invisible". The contrast run above proves the new check is not
blanket-refusing: with the placeholder gone the same tree is walked and the
spec is collected and executed (that fixture spec's own failure is unrelated —
it is a bare three-line fixture with no spec header).

### Spec

Extended `test/01_unit/app/test_runner_strip_ansi_spec.spl` (the existing unit
spec for this same module — no new file):
`describe "is_symlink_placeholder"` / `it "flags a degraded symlink placeholder
and never a real source file"`. It writes a placeholder shaped exactly like a
`core.symlinks=false` checkout and asserts `true`, then asserts `false` on real
Simple source in the same walk.

```
$ SIMPLE_BINARY=$B $B test test/01_unit/app/test_runner_strip_ansi_spec.spl ; rc=$?
rc=0
SPEC FILE VERDICT: ... outcome=OK declared>=13 executed=13 passed=13 failed=0 skipped=0 dropped=0
Results: 13 total, 13 passed, 0 failed
```

(12 pre-existing `strip_ansi` examples + the 1 new one.)

Two-spec rule: the reproducing/generalizing pair filed with the sibling fix —
`test/03_system/check/windows_symlinked_spl_readable_as_code_spec.spl` and
`test/03_system/check/windows_dangling_symlink_fails_loudly_spec.spl` — remain
the coverage for the materialisation half; the `it` above covers the
dir-mode-detection half added here.

### NOT verified / still open

- **`simple test test/01_unit/lib/std/` is still red on this box, for an
  unrelated reason.** After materialisation the symlink wall is gone (the run
  now reaches `compiler.backend.linker.*`), and it stops at
  `src/compiler/00.common/structural_contracts/frontend_offload_switch.spl:47`
  with `function arguments: expected Comma, found Colon` on
  `FrontendOffloadSwitch(mode: mode, auto: auto, ...)`. That is the `auto`
  named-argument-label defect fixed 2026-09-05 in
  `auto_keyword_rejected_as_named_argument_label_2026-09-05.md`, which
  explicitly **requires a rebuilt seed**; the seed available here predates it.
  Separate blocker, not this bug.
- Unix behaviour is unchanged by construction (the detector requires a
  whitespace-free single-line body that only a degraded checkout produces — on
  Linux/macOS a real symlink resolves and `dir_walk` returns the target's
  contents), but that was **not** executed from this Windows host and is stated
  rather than claimed.
- The daemon-import-graph half of the original symptom is fixed only by running
  the materialiser; nothing yet runs it automatically on an ordinary developer
  checkout. Candidate follow-up: call it from `scripts/setup/setup.shs`.
