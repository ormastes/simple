# Stage-2 import resolution and `compile` harness: four independent defects

**Date:** 2026-08-24
**Found by:** lane E3 (backend/frontend/mir_opt/types Stage-3 scope), while verifying
import fixes against the admitted Stage-2 binary.
**Binary under test:** `build/bootstrap/goal-stage2/stage2/x86_64-unknown-linux-gnu/simple`,
built 2026-08-24 01:34:11, 132,944,880 bytes.
**Status:** all four OPEN. None is fixed by the import corrections that ship alongside
this record — those fix *source* debt; these are defects in the compiler and its
`compile` entry path.

These were found incidentally and are filed rather than mentioned in passing, because
three of them actively mislead anyone debugging Stage 3: two make a broken run *look*
clean or *look* like a path typo, and one prints a symbol name that does not exist in
the source.

---

## Defect 1 — a mangled name in a diagnostic: `unresolved name: __p-1` for `env_get`

**Severity: highest of the four.** This is the only one where the compiler reports a
symbol that appears nowhere in the program, so the message cannot be acted on.

`src/compiler/10.frontend/core/parser_decls_use.spl:58:16` is:

```
    if env_get("SIMPLE_PARSE_PROFILE") == "":
```

Column 16 is `env_get`. Stage 3 reports, three times:

```
HIR lowering error in src/compiler/frontend/core/parser_decls_use.spl:
  unresolved name: __p-1 at src/compiler/frontend/core/parser_decls_use.spl:58:16
```

`__p-1` is not a name in this file, in its imports, or anywhere in the tree. It reads
as a desugar temporary `__p` with an index of `-1` — i.e. an unset/sentinel index that
was formatted into a diagnostic instead of the real identifier.

**This is NOT the missing-import class.** `env_get` **is** explicitly imported, at
line 38 of the same file:

```
use std.nogc_sync_mut.io_runtime.{env_get, time_now_unix_micros}
```

and `std.nogc_sync_mut.io_runtime` really does define it (`io_runtime.spl:275`,
`pub fn env_get(key: text) -> text`). So the name is imported, the provider exports
it, and resolution still fails — with a fabricated name. Two bugs are plausibly
stacked here: a resolution failure for an explicitly imported `std` symbol, and a
diagnostic that renders a desugar temp rather than the source identifier.

Because the reported name is fabricated, the usual fix (add the import) is not
available and grepping for the reported symbol finds nothing — which is exactly how
this could burn hours. Owner: the HIR-lowering / name-resolution lane.

Reproduce: lower `src/compiler/frontend/core/parser_decls_use.spl` with the Stage-2
binary and read the three `unresolved name: __p-1` lines.

---

## Defect 2 — `compile` on a *numbered* path fails entry collection; the symlink spelling works

`src/compiler/` carries 17 git-tracked symlinks (`frontend -> 10.frontend`,
`backend -> 70.backend`, `mir_opt -> 60.mir_opt`, `types -> 30.types`, …). The two
spellings name the *same physical file*. `compile` accepts only one of them:

```
$ simple compile src/compiler/10.frontend/treesitter/outline_decls.spl --format=smf -o /tmp/o.smf
[ERROR] phase 1 FAILED
error: in-process SMF compile: native-build entry
  'src/compiler/10.frontend/treesitter/outline_decls.spl' collected zero source files:
  --entry takes a path to a .spl file (e.g. 'dir/main.spl'), not a module path
  (e.g. 'dir.main'), and the path is resolved relative to the current working directory

$ simple compile src/compiler/frontend/treesitter/outline_decls.spl --format=smf -o /tmp/o.smf
   # collects sources and lowers normally
```

Same file, same cwd, both paths exist and both resolve on disk. Reproduced on
`10.frontend/treesitter/outline_decls.spl` and `10.frontend/treesitter/heuristic.spl`.

**Why this is a trap, not a cosmetic complaint:** the error message asserts a
*diagnosis* — "you passed a module path, not a file path" — that is false. The
argument given IS a file path to an existing `.spl` file. The likely mechanism is that
the numbered component (`10.frontend`) contains a `.` and is being treated as a
module-path separator, so the entry is rejected before the file is ever stat'd. A
person debugging Stage 3 naturally uses the numbered path, because that is the real
directory and the one `git`/`ls` show, and gets told their invocation is malformed.

The message should either accept the path or, at minimum, not state a cause it has not
checked (an existing file on disk should never be reported as "not a path to a .spl
file").

---

## Defect 3 — standalone `compile` on any compiler source SEGVs after lowering

Every single-file `compile` of a `src/compiler/**` source ends `rc=139` (SIGSEGV),
*after* HIR lowering of the entry module has completed and its counters have printed:

```
[bootstrap-error-count] source_idx=0 point=post-lowering count=0
[bootstrap-error-count] source_idx=0 point=post-diagnostics count=0
timeout: the monitored command dumped core
```

Observed on all 13 files exercised for this landing, on both spellings, at both this
worktree's base and at `origin/main 8f4a17a6fc6`.

**Cross-reference:** on a minimal two-file fixture (not a compiler source) the same
binary instead fails cleanly with

```
error: hir codec: no `Visibility` arm for tag -1; regenerate src/compiler/20.hir/generated/hir_codec.spl
```

which is the same `Visibility`-codec defect reported for the two-line hello world, and
which `7c453e7b076` post-dates this binary by ~4 hours. The SEGV and the codec error
plausibly share a root cause — a `Visibility` tag of `-1` reaching a decode that has no
arm for it — with the compiler-source path crashing where the fixture path raises.

**Consequence for verification method, and why it is safe:** single-file lowering
checks must read the `post-lowering` counters and treat the later crash as out of
scope. That is sound *only* because the counters are printed before the crash and are
per-module. It is **not** sound to read a crashed run's *absence* of errors as success
— see Defect 4.

---

## Defect 4 — a crashed run reports zero errors, and that silence has already been misread

Not a compiler defect so much as a reporting one, recorded because it produced a wrong
conclusion that was acted on.

A Stage-3 re-measure was reported as "0 lowering errors at HEAD" and used to conclude
that the 405-error blocker was stale. The run that produced it SEGVd at
`[build] hir 0/692` — at the very start of HIR. **Zero of 692 modules lowered.** No
module having been lowered, no lowering error could be emitted, and the run's silence
carried no information.

This is precisely the trap `.claude/rules/testing.md` already pins for test runs ("a
run that executed nothing is UNKNOWN, never a pass"); the lesson is that it applies to
a "0 errors" claim exactly as it does to a "0 tests failed" one.

The positive control that settles the question: a detached worktree at
`origin/main 8f4a17a6fc6`, compiled with that same admitted Stage-2 binary, reproduces
**8 `unresolved name: methods_push` + 2 `fields_push`** in
`src/compiler/frontend/treesitter/outline_decls.spl` — byte-matching the counts in
`/mnt/data/goal-logs/stage3-failure.log`.

**Guidance:** any Stage-3 verdict must state how many of the 692 modules actually
lowered. A run that lowered 0 is UNKNOWN. Prefer a *positive* control — reverting a
known fix must reproduce a known error count — over an absence of errors, since only
the positive control proves the harness can see the thing it is claiming is gone.

---

## Two hypotheses tested and DISPROVEN (recorded so they are not re-chased)

- **Duplicate compiler module trees.** The 17 symlinks do cause each file to be
  enumerated under two path spellings, but HIR dedup is sound: the Stage-3 log shows
  **692 modules and 0 duplicate module ids**.
- **Spelling-split package scope** (a package cut in half because some members
  registered under `70.backend/…` and others under `backend/…`). Every failing file
  and its defining sibling registered under the **same** spelling and the same module
  prefix. No package was split.
