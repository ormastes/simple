# Deployed seed resolves `src/lib` stdlib from a FOREIGN worktree first

- **Date:** 2026-08-20
- **Status:** RESOLVED (2026-08-21) — behaviour re-verified green on the current seed, one real baked-path precedence bug fixed, and a fail-closed behavioural guard added so a recurrence cannot pass unnoticed
- **Severity:** high (silently executes another session's stdlib; edits to this tree's `src/lib/**` are invisible)

## Symptom

From `/mnt/data/worktrees/simple-main`, `bin/simple run <probe>` executed the
OLD body of `_access_ensure` in `src/lib/common/ui/access_query.spl` even after
the file was edited, and even with a deliberate marker string inserted
(`count_mismatch: XPROBE`) — the marker never appeared in output. Edits to
`src/app/**` in the same runs WERE picked up.

## Root cause (measured)

`strace -e openat` on the run shows the interpreter opens BOTH:

```
/mnt/data/worktrees/render-harden/src/lib/common/ui/access_query.spl   (first, line 264)
/mnt/data/worktrees/simple-main/src/lib/common/ui/access_query.spl     (later, line 531)
```

and the render-harden copy wins for module `common.ui.access_query`. The trace
also shows probes of
`/mnt/data/worktrees/render-harden/src/compiler_rust/compiler/../../../src/lib/variants/...`,
i.e. the deployed seed (`bin/release/x86_64-unknown-linux-gnu/simple`) was
built inside the render-harden worktree and carries its build tree
(`CARGO_MANIFEST_DIR`-style baked path) as a stdlib search root that is
consulted BEFORE the current repo's `src/lib`. 138 render-harden opens in one
run. `SIMPLE_LIB` does not override this (only read by `memory_guard.rs`).

## Impact

- The CLAUDE.md claim "a `src/lib/**` edit needs NO build — stdlib is read as
  SOURCE every run" is true but resolves the WRONG tree when the deployed seed
  was built in a different worktree: lib edits in this tree are silently
  ignored wherever the foreign tree also has the module.
- Verification of `src/lib` changes (here: input hardening in
  `access_query.spl` `_access_ensure` match_count validation) is blocked from
  this worktree until the seed is rebuilt/redeployed from this tree or the
  baked root is deprioritized below the invoking repo's `src/lib`.

## Unblock condition

Module resolution must prefer the current project root's `src/lib` over any
compile-time baked source root; or redeploy a seed built in this worktree.

## Related spec

`test/01_unit/app/office/sheets/access_controller_spec.spl` —
"fails closed on a non-numeric match_count expectation" asserts the new
guard's reason text and stays RED under the foreign-tree stdlib.

## Resolution (2026-08-21)

### 1. Re-measured on the current seed — the symptom is gone

Binary: `bin/release/x86_64-unknown-linux-gnu/simple` (2026-08-21 14:27:35,
59,947,080 bytes). `strings` shows **0** occurrences of `worktrees/render-harden`
(the old baked root) — the current seed's baked path is
`/mnt/data/worktrees/landperf`, 776 occurrences. `strace -e openat` on a run that
imports `std.common.text` shows **29 opens under
`/mnt/data/worktrees/simple-main/src/lib` and zero under any other worktree**.

That is a re-measurement, **not** a proof of fix: `landperf/src/lib` does not
currently exist on disk, so this particular binary cannot express the defect
even if the precedence were still wrong. Absence of the symptom under a
non-reproducing configuration is not evidence, which is why the two items below
exist.

### 2. Real defect found and fixed: baked path OUTRANKED the invoking tree

`find_unit_tree_root()` (`src/compiler_rust/compiler/src/units/registry.rs`) —
the resolution root for `use unit.*` — built its candidate list with the
compile-time `CARGO_MANIFEST_DIR` climb FIRST and the cwd climb second, so a
binary built in worktree A and run in worktree B read A's unit tree whenever A
still existed on disk. Same defect class as the reported `src/lib` symptom, same
mechanism, in a path nobody had checked. Reordered: explicit
`SIMPLE_UNIT_TREE_ROOT` override, then the invoking worktree, then the baked
path as a genuine last resort (it is still needed under `cargo test`, where cwd
is a crate directory). `cargo check --release -p simple-compiler` clean.

For `src/lib` itself no baked root remains in the resolution path:
`resolve_module_path_uncached` / `resolve_unit_module_path`
(`interpreter_module/path_resolution.rs:780-810`) build their search roots from
`find_project_root(base_dir)` and the cwd's project root only, and every other
non-test `CARGO_MANIFEST_DIR` use in the shipped crates is inside `#[cfg(test)]`
or a link/tool path, not module resolution.

### 3. Fail-closed behavioural guard

`scripts/check/check-stdlib-resolves-from-invoking-worktree.shs` — it RUNS the
binary rather than inspecting the tree, because this was never a structural
property. Three probes: (1) a throwaway project's own marked `src/lib` module
must be used; (2) a **decoy** project carrying the same module path with a
different marker (pointed at via `SIMPLE_LIB`) must NOT win — this is the
incident's exact shape and is what makes the check more than a smoke test; (3)
under `strace`, no `src/lib` path outside the invoking project root may be
opened at all. Without `strace` leg 3 reports as skipped, never as pass. 0
probes, or a missing binary, is `ERROR — nothing was checked` (exit 2).

`--selftest` (5 fixtures, fatal, runs before every scan) includes a synthetic
strace fixture proving the foreign-open detector isolates a `render-harden`
path and ignores the local one — otherwise leg 3 could report "0 foreign opens"
because its expression matches nothing.

Measured now: `PASS — 3 probe(s) executed, stdlib resolved from the invoking
worktree (open-path leg ran: 0 src/lib opens outside the invoking project root)`.
