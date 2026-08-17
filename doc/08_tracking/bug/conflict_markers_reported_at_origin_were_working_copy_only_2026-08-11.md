# Conflict markers reported "committed at origin" were WORKING-COPY ONLY (stalled cherry-pick)

- Date: 2026-08-11
- Status: CLOSED (not reproducible)
- Status re-verified 2026-08-17 by source inspection (triage shard 00).
- Reported as: "commit `57ed3ef0365` committed literal git conflict markers into
  `src/runtime/runtime.h` (lines 1, 1271, 2406) at origin; every seed cargo build now fails."
- Actual: the markers exist only in the **uncommitted, unmerged working tree** of
  `/home/ormastes/dev/pub/simple`. They were never committed and never pushed.

## Evidence

Origin tip at time of investigation: `21315d9aac`.

```
git show origin/main:src/runtime/runtime.h | grep -cE '^(<<<<<<<|>>>>>>>)'   -> 0
git show 57ed3ef0365:src/runtime/runtime.h | grep -nE '^(<<<<<<<|>>>>>>>)'  -> (no output)
```

A full-tree marker sweep of BOTH `57ed3ef0365` and `origin/main` returns exactly two
files, both vendored jj documentation that legitimately *documents* marker syntax:
`src/compiler_rust/vendor/jj-cli/docs/conflicts.md` and `.../docs/tutorial.md`.
Zero product files carry markers in either commit.

## Root cause: a stalled `git cherry-pick` in the shared working copy

The repo at `/home/ormastes/dev/pub/simple` is a **plain git repo, not colocated jj**
(`jj log` -> "There is no jj repo in ."). State found:

- `.git/CHERRY_PICK_HEAD` **present** (no `MERGE_HEAD`, no `rebase-merge`, no `rebase-apply`)
- `HEAD` = `cf847f7c2a3` (local-only commit, not at origin)
- Picked commit = `a2bff98dd70` "fix(runtime): preserve u64 across erased values", which is
  **not an ancestor of origin/main nor of HEAD**
- 12 product files in `UU` (both-modified) state with stage 1/2/3 index entries

The marker trailer in every offender is `>>>>>>> a2bff98dd70 (fix(runtime): preserve u64
across erased values)` — git cherry-pick's conflict format, confirming a single origin.

### Offender list (12 files, all working-copy-only, all `UU`)

| file | WC lines | origin lines |
|---|---|---|
| `src/compiler_rust/compiler/src/codegen/llvm/functions/casts.rs` | 150 | 97 |
| `src/compiler_rust/compiler/src/codegen/runtime_sffi.rs` | 2216 | 2212 |
| `src/compiler_rust/runtime/src/value/collections.rs` | 6016 | 5998 |
| `src/compiler_rust/runtime/src/value/core.rs` | 696 | 635 |
| `src/compiler_rust/runtime/src/value/heap.rs` | 749 | 733 |
| `src/compiler_rust/runtime/src/value/mod.rs` | 1186 | 1179 |
| `src/compiler_rust/runtime/src/value/sffi/equality.rs` | 901 | 878 |
| `src/compiler_rust/runtime/src/value/sffi/value_ops.rs` | 304 | 242 |
| `src/runtime/runtime.h` | 2406 | 1273 |
| `src/runtime/runtime_native.c` | 10316 | 10501 |
| `src/runtime/simple_core/core_array_query.spl` | 348 | 341 |
| `test/01_unit/runtime/runtime_native_focus_test.c` | 610 | 584 |

## Why no repair was landed

Resolving these means choosing sides for **another concurrent session's live, in-flight
cherry-pick**. Per `.claude/rules/` ("don't touch a file another concurrent session is
midflight on") and because the picked commit `a2bff98dd70` exists nowhere in published
history, a third party cannot reconstruct the intended resolution without destroying that
session's work. Origin needs no repair. The owning session must finish or
`git cherry-pick --abort` its pick.

## Red-then-green proof

Red — the working-copy `runtime.h`:

```
$ gcc -fsyntax-only -I. rth_probe.c        # rth_probe.c = #include "runtime.h"
./runtime.h:1:1: error: version control conflict marker in file
    1 | <<<<<<< HEAD
```

Green — the same file at origin tip `21315d9aac`, in a clean isolated worktree
(`/mnt/data/verify-origin-tip`):

```
$ gcc -fsyntax-only -I. rth_probe.c ; echo exit=$?
exit=0
```

Green — the full seed driver build the report claimed was broken:

```
$ CARGO_TARGET_DIR=/mnt/data/cargo-target-rthfix \
  cargo build --manifest-path src/compiler_rust/Cargo.toml --release -p simple-driver --bin simple
    Finished `release` profile [optimized] target(s) in 4m 00s
```

Warnings only (3 pre-existing `simple-compiler` lib warnings), zero errors. This also
**verifies `21315d9aacc` "fix(cli): wire stats/doc-coverage into seed COMMAND_TABLE"**,
which was previously unverifiable — it builds clean.

## Why the pre-push marker guard "missed" it — it did not

`scripts/check/check-no-conflict-markers-push.shs` scans the **outgoing commit range**
(`main@origin..@-`). No marker ever entered a commit, so there was nothing in range to
flag. The guard behaved correctly; this is a false alarm, not a guard gap.

The real gap is diagnostic, not preventive: **the report grepped the working tree and
attributed the result to a commit.** A working-tree grep says nothing about what is
published. Standing lesson, same family as
`reference_diff_wc_against_head_before_blaming_source`:

> Before declaring "commit X broke origin", read the content **from the commit**
> (`git show <sha>:<path>`), never from the checkout. A shared working copy is routinely
> mid-operation for some other session.

### Filed (not fixed this pass)

Optional hardening, deliberately not implemented here: a cheap pre-build/pre-report
tripwire that reports `.git/CHERRY_PICK_HEAD` / `MERGE_HEAD` / `rebase-*` presence and any
`git ls-files -u` entries, so an in-flight operation is named as the cause instead of
being misattributed to a published commit. Not a one-liner in guard terms; filed here.
