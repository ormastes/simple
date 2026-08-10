# A2 target IR is complete but NOT landed — blocked on an untracked file

**Date:** 2026-08-10
**Status:** OPEN — work is done and passing, deliberately withheld from `main`.
**Work location:** worktree `.claude/worktrees/agent-a5cdacdf7286b11a3`, branch
`worktree-agent-a5cdacdf7286b11a3` (do not delete this worktree).
**Plan:** `doc/03_plan/compiler/build_system/targeted_build_interface_compat_minimal_bootstrap_2026-08-10.md` §5/§6, Wave 1.

---

## What is done

Agent A2 delivered the complete Wave-1 target IR, compute-only:

- `TargetKind` (9 kinds) and `DependencyEdgeKind` (all 9 typed edges from plan §6)
- The `Target` record exactly per plan §5.2
- `TargetLabel` + `parse_target_label` / `target_label_to_text` — `//path:name` plus bare
  aliases; rejects missing `:name`, empty name, `/`-without-`//`, and multiple `:`
- A `build.sdn` reader (dedicated line/indent parser, because SDN's `parse()` drops block
  sequences of mappings — a bug documented in the existing file itself)
- `synthesize_legacy_target(entry_file, source_roots, output)` for CLI-flag compatibility
- `TargetGraph` with `target_graph_deps` / `target_graph_rdeps`

**Verdict:** `SPEC FILE VERDICT: test/01_unit/compiler/build_graph/target_graph_spec.spl
declared>=9 executed=9 passed=9 failed=0 dropped=0` — reproduced by the reviewing model
in A2's worktree, not merely relayed. Two sabotage probes confirmed RED then GREEN
(rdeps returning the forward closure; malformed `//path` silently accepted).

Non-goals respected: no CLI dispatch touched, `--target` still means a platform triple,
no bootstrap scripts touched, nothing wired into build selection.

## Why it is not landed

A2 authored this as an **append** to `src/compiler/80.driver/cache/target_graph.spl`.
That file is **not tracked in git** — `git cat-file -e <origin-tip>:…/target_graph.spl`
exits 128, and `git status` shows it as `??`. It is a concurrent session's **untracked,
in-flight work** (281 lines: a manifest-dir dependency graph with cycle detection).

Landing A2's version would have committed another session's unfinished file under this
change — exactly what `.claude/rules/vcs.md` and
`feedback_dont_touch_a_file_another_concurrent_session_is_midflight_on` forbid.

## Why the standalone-extraction workaround was rejected

The reviewer attempted to extract A2's section into a standalone
`80.driver/build_graph/target_ir.spl` so it could land without touching the other
session's file. That attempt **failed its own test** — `executed=9 passed=8 failed=1`,
the `build.sdn` reader case — and was reverted from the working tree.

Cause: the new section depends on **three** helpers defined in the original 281 lines,
not one:

| helper | size | verdict |
|---|---|---|
| `target_path_normalize` | ~20 lines | generic, duplicable |
| `_indent_of` | 8 lines | generic, duplicable |
| `_dep_paths_from_text` | ~20 lines | **parses the manifest `dependencies:` block — belongs to the ORIGINAL section, not this one** |

Forking three helpers — one of which is semantically owned by the other section — to dodge
a temporary concurrency conflict is a worse outcome than waiting. It would create an
immediate consolidation debt and a second copy of a parser that must not diverge.

## Unblock condition

When the concurrent session commits `src/compiler/80.driver/cache/target_graph.spl`:

1. Rebase the A2 worktree onto the new `main`.
2. Confirm the committed original 281 lines still match what A2 appended to
   (`diff <(head -281 <a2-file>) <(git show main:…/target_graph.spl)`) — if the other
   session changed them, re-apply A2's section on top of THEIR version, never overwrite.
3. Re-run the spec; require `executed=9 passed=9`.
4. Land only the appended section as a forward delta.

**Do not** land A2's 668-line file wholesale at any point — it embeds a snapshot of the
other session's work as of 2026-08-10 and would revert whatever they did afterward.
