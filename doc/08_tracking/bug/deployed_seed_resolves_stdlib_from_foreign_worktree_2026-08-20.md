# Deployed seed resolves `src/lib` stdlib from a FOREIGN worktree first

- **Date:** 2026-08-20
- **Status:** OPEN
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


## Round 15 note (2026-11-07, work/r15-stdlib-20261107)

Same evidence and gate as deployed_binary_reads_stdlib_from_its_build_worktree_2026-08-25: scripts/check/check-stdlib-invoking-tree-wins.shs.

## 2026-11-10 status — SUPERSEDED (P3 library lane, work/p3-lib-20261110)

Same root cause and same gate as
deployed_binary_reads_stdlib_from_its_build_worktree_2026-08-25; same result on
this lane's base: `check-stdlib-invoking-tree-wins.shs --selftest <deployed
seed>` → `PASS -- 1 probe, invoking tree's src/lib won`. The baked
build-worktree search root no longer wins over the invoking repo's `src/lib`.

## 2026-11-11 status — SUPERSEDED (P3-essential library lane, work/p3-lib3-20261111)

Same root cause and same gate as
deployed_binary_reads_stdlib_from_its_build_worktree_2026-08-25; verdict
re-confirmed on this lane's refreshed seed (bin/simple.exe, build-commit
`0791c2b7f4a7`): `check-stdlib-invoking-tree-wins.shs --selftest
"$PWD/bin/simple.exe"` → `PASS -- 1 probe, invoking tree's src/lib won
(rc=0)`. The `_access_ensure`-era foreign-tree-wins behaviour does not
reproduce.
