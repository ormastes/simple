# Dirty-working-copy triage: 1,525 files left by ~20 spend-limit-killed sessions

Date: 2026-08-17. Landed as `d7213eb6174` (src, 69), `fb87405c18e` (test, 160),
`a9a463eb061` (scripts, 25), `2868222ffbc` (docs, 1053).

Method: per-file forward-vs-rewind classification, `GIT_INDEX_FILE` plumbing from
an explicit `BASE`, CAS publish, `git diff-tree -r --name-status` audit on each
landed sha. No `git add -A`, no `commit -a`, no `commit-tree -p HEAD`. The docs
batch's first CAS **failed** (`main` moved to `bcb3218ec5e` mid-operation); the
list was re-derived against the new tip and retried. That is the CAS working.

## `D` in `git diff HEAD` does NOT mean the file is gone from disk

The shared index is stale because every lane commits via `GIT_INDEX_FILE`
plumbing that bypasses it. A path present in `HEAD` but absent from the *index*
is reported `D` by `git diff HEAD` and `git status` while existing on disk.

Measured: 214 paths added by this lane's own four commits all reported `D`
immediately afterwards, and **all 214 were present on disk** (`present=214
absent=0`).

Consequence for anyone hunting today's deletion incidents: **a `D` line is not
evidence of a deletion.** Confirm with `[ -f "$path" ]` before acting. This lane
initially misread 65 such entries as rewinds and ran `git checkout HEAD --` on
them. All 65 are now present and byte-identical to `HEAD` and nothing is missing
repo-wide, but if any had carried newer on-disk edits, that checkout destroyed
them and it cannot be proven otherwise — there is no jj repo in this worktree, so
no working-copy snapshots exist to recover from. Recorded here rather than left
for someone to find.

## Dropped working-copy content: 10 files, with evidence

Per "MERGE, DO NOT REMOVE", each of these was dropped in favour of the committed
`HEAD` content because the working-copy version was a demonstrably WRONG rewind —
verified by reading the diff content, never by SHA ancestry. None was dropped for
looking stale, conflicted, or foreign.

| file | what the working copy deleted | why that is wrong |
|---|---|---|
| `compiler/src/interpreter/expr/ops.rs` | `fn unsigned_ordering` entire, plus its bug-doc comment and all four ordering-arm call sites | It is the u64-high-bit comparison fix. Without it `0x8000_0000_0000_0000u64 > 0u64` is `false` in the interpreter and `true` in JIT/native — the exact cross-engine silent divergence the row was filed for. Its own reproducing spec (`test/01_unit/language/u64_high_bit_ordering_comparison_spec.spl`) was absent from the working copy too. |
| `runtime/src/value/core.rs` | `HeapObjectType::UInt` arms in `type_name`/`ValueKind`, the `TAG_HEAP` channel match, the `<< 3` boxing comment | Part of `fix(jit): i64 values >= 2^60 silently became a different number`. |
| `runtime/src/value/heap.rs` | `HeapObjectType::UInt => ValueKind::Int` | Same fix. Deleting the arm while the variant remains defined is not a valid state. |
| `runtime/src/value/transfer.rs` | `EncodedLeafKind::UInt64` length arm, the `payload_is_valid() && checksum` guard | Same fix. Dropping the checksum guard re-opens a fail-open transfer path. |
| `runtime/src/value/sffi/value_ops.rs` | `rt_dict_*` / `rt_enum_*` imports | Same fix. |
| `interpreter_call/core/class_instantiation.rs` | `should_call_new` / `all_named_struct_literal` | Reverts `fix(interpreter): stop auto-routing fully-named struct literals to a name-coincident static new`. |
| `parser/src/expressions/postfix.rs` | struct-form `Expr::UnwrapOrReturn { expr, default }`, replaced with the tuple form `UnwrapOrReturn(Box::new(expr))` | The tuple form is the `E0533` break another lane repaired at `postfix.rs:613`. The working copy was the broken side. |
| `interpreter_call/builtins.rs` | the `inclusive` argument evaluation | Removes a range builtin's third parameter. |
| `scripts/bootstrap/bootstrap-from-scratch.sh` | stage2-capability warning line | Reverts `fix(bootstrap): progress heartbeat on by default`. |
| `scripts/check/check-bootstrap-progress-watch.shs` | the fixture/busy/idle `kill` cleanup lines | Reverts `test(bootstrap): make the heartbeat guard's busy/idle thresholds load-robust`. |

Verified after restore, all present in `HEAD`: `unsigned_ordering`,
`HeapObjectType::Int`, `as_heap_i64`, struct-form `UnwrapOrReturn`.

## Not landed, not work

`src/compiler_rust/target_wt/` (2,255 cargo artifacts), 9 root-level
`*_probe_tmp.spl` / `v9_*_probe.spl`, `scratch_p1/`, `src/app/_scratch_ed/`,
`test/tmp_repro/`, `.claude/worktrees*`, `map.smf.jit.note.sdn`. Left dirty
rather than deleted — dropping them from disk is not this lane's call.

## Tree health after landing

114,906 files (band 90,000–150,000); `src/` 16 entries (band 13..25);
`src/runtime` 218 files (canary >= 150).
