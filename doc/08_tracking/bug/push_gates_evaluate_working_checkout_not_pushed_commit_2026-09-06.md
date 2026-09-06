# `tree`-mode push gates evaluate the working checkout, not the pushed commit

- **Filed:** 2026-09-06
- **Class:** fail-wrong guard (same family as
  `pre_push_guards_fail_open_on_cwd_2026-08-01.md`, but the opposite failure —
  these guards *do* check something, they check the wrong tree)
- **Status:** one gate fixed (`push-rt-dual-implementation`), the class remains
  open for the other 16 `tree`-mode rows.

## Symptom that made this real

On 2026-09-06 a 12-PR chain-merge was pushed directly to `main` with
`--no-verify`. The reason given at the time was "the hook is failing on a stale
baseline". That diagnosis was wrong, and the guard's own design is what made it
plausible: the pre-push hook reported a failure describing content in the shared
working checkout, while the content actually being pushed carried two *different*
regressions that the same run never looked at.

Both real regressions (`push-rt-dual-implementation` and
`push-runtime-source-list-parity`) landed on `main` unblocked. A guard that
reports on the wrong tree is worse than no guard: it produces a failure the
operator learns to route around, and then it is silent about the one that matters.

## Mechanism

`.git/hooks/pre-push` -> `scripts/hooks/pre-push` ->
`scripts/check/pre-push-conflict-tree-guard.shs` -> `exec sh
scripts/check/check-push-must-pass.shs --from-pre-push-hook`. The authoritative
surface is the `push,`-tier rows of `config/check/must_check_gates.sdn`, executed
by `run_manifest_push_gates`.

That function supports three modes:

| mode | what the dispatcher passes | what the gate reads |
|---|---|---|
| `range` | `"$_range"` | committed content of the outgoing range |
| `ref` | `--rev "$_ref"` / `--ref "$_ref"` | committed content of the pushed tip |
| `tree` | *nothing* | **the working checkout** |

A `tree` row is invoked with no revision at all, so the gate defaults to
`git rev-parse --show-toplevel` and scans whatever happens to be on disk. On this
machine roughly ten agent sessions share one clone, so "whatever happens to be on
disk" is routinely neither the pushed commit nor any commit.

`tree` mode is defensible for a gate whose subject genuinely has no committed
form (`check-c-runtime-compiles-push.shs` compiles a tree; runnability of a
binary is a property of an artifact). It is **not** defensible for a gate whose
subject is committed source, which is the case for most of the 17 rows.

## Reproduction

```sh
# In a clone with a dirty working copy:
printf 'pub fn rt_working_copy_only() -> i64 { 9 }\n' \
  >> src/compiler_rust/runtime/src/lib.rs        # never committed

sh scripts/check/check-rt-dual-implementation-ratchet.shs           # sees the edit
sh scripts/check/check-rt-dual-implementation-ratchet.shs --rev HEAD # does not
```

Before the fix below, the pre-push hook ran the first form. This is now pinned as
selftest fixture 7 of that script, which commits a clean tree plus a matching
baseline, dirties the working copy with a new rust-only symbol *and* a baseline
row that would excuse it, and asserts that `--rev HEAD` reports
`2 symbol(s) checked ... 0 new, 0 stale` while the working-tree scan reports
`3 symbol(s) checked ... 0 new, 0 stale`. The fixture fails if the two paths ever
agree, so it cannot rot into a tautology.

## Fix applied (this change) — one gate

`push-rt-dual-implementation` moved from `tree` to `ref`:

- `config/check/must_check_gates.sdn`: mode `ref`, command
  `"sh scripts/check/check-rt-dual-implementation-ratchet.shs --rev"`.
- `scripts/check/check-push-must-pass.shs`: the dispatch case label is updated to
  the new `id:mode:command` key and passes `--rev "$_ref"`. The manifest row and
  the case must byte-match or the fail-closed `*)` arm blocks every push; the
  match was verified by replaying the dispatcher's own field parsing against the
  edited row.
- `scripts/check/check-rt-dual-implementation-ratchet.shs`: **the baseline is now
  archived out of the same revision.** Scanning committed sources while comparing
  them against the working copy's baseline is still a wrong-tree verdict — a
  local edit to the baseline, or a checkout predating a baseline update, would
  decide the result for content it does not describe. `--generate-baseline` with
  `--rev` and no explicit `--baseline` is now a hard ERROR rather than a silent
  write into the throwaway archive directory.

`sh scripts/check/check-guard-wiring.shs` still passes after the row change.

## NOT fixed — the rest of the class

The other 16 `tree` rows still scan the working checkout. They split into two
groups:

- **Genuinely tree-scoped** (correct as-is): `push-c-runtime-compiles`.
- **Committed-source subjects that should be `ref`**, none of which currently
  accept a revision at all — they take only `--root`:
  `push-runtime-source-list-parity`, `push-no-direct-rt`,
  `push-interpreter-extern-registry-gap`, `push-sffi-v2-authority`,
  `push-type-walk-constructor-parity`, `push-guard-wiring`,
  `push-parser-source-global-ratchet`, and the advisory rows.

Each needs a `--rev` implementation (materialise via `git archive` into a temp
dir, exactly as the rt-dual guard now does) before its manifest row can move.
That is mechanical but touches eight scripts, so it is filed rather than
attempted here. Until then, treat a `tree`-row verdict as evidence about the
machine, not about the push.

## Rule that should follow

A guard whose subject is committed source must read committed content. A guard
that cannot be handed a revision must say so in its header and must be filed
here, so `tree` never silently becomes the default for a gate that could have
been `ref`.
