# `tree`-mode push gates evaluate the working checkout, not the pushed commit

- **Filed:** 2026-09-06
- **Class:** fail-wrong guard (same family as
  `pre_push_guards_fail_open_on_cwd_2026-08-01.md`, but the opposite failure —
  these guards *do* check something, they check the wrong tree)
- **Status:** 2026-09-16: 11 blocking rows fixed (six on 2026-09-07 via PR
  #465, commits 45f16f29027, ca867521f93, 13a831908ae, plus the five
  spirv-pinned rows this sweep — see the update section below). Zero
  blocking `tree` rows remain; the class stays OPEN for the 35 advisory
  `tree` rows and for the generic mechanism question about tree rows whose
  subjects have no committed form.

## 2026-09-16 update (macOS sweep)

Progress on this class: the five blocking `spirv-pinned` rows that were
added as `tree` rows after the original census — `push-rect-batch-spirv-pinned`,
`push-blit-spirv-pinned`, `push-blur-rect-spirv-pinned`,
`push-shadow-rect-spirv-pinned`, `push-glass-material-spirv-pinned` — moved
from `tree` to `ref`. Their subjects are committed content (regenerate from
checked-in GLSL, compare against checked-in SPIR-V words), which per the rule
in this file belongs on `--rev`. The dispatcher mechanism note above (the
three-mode table and the `run_manifest_push_gates` dispatch) is unchanged and
still accurate.

What the conversion carries, identical to the established pattern from
`check-rt-dual-implementation-ratchet.shs` / PR #465:

- `--rev <REV>` materialises the committed GLSL source and pinned SPIR-V
  blob with `git archive <REV> -- <paths> | tar -x` into a temp dir at the
  pushed sha, and the scan runs there. The transcription tool
  (`scripts/tool/spirv-to-spl-words.shs`, plus
  `scripts/tool/extract-blit-glsl.shs` for blit) is archived from the same
  rev — the tool is itself content, and a working-copy tool sabotage
  deciding a committed-content verdict is the same wrong-tree defect one
  level down.
- Fail-closed throughout: a failed or incomplete materialisation is
  `ERROR — nothing was checked (could not materialise <rev>)`, exit 2, never
  a pass. Default no-arg behavior is unchanged (working checkout).
- A selftest fixture that asserts the two paths DISAGREE (rect-batch,
  blur-rect, shadow-rect, glass-material fixture 5; blit fixture 6): commit
  a matching pair, dirty the working copy with an unregenerated GLSL edit,
  and require `--rev HEAD` to PASS while a working-tree scan of the same
  directory FAILs. The fixture is fatal before every scan, so it runs on the
  push path. These guards have no baseline/allowlist file, so the census's
  second rot axis (data file reverting to the checkout) has no surface; the
  tool axis was injected separately, below.

Verification on macOS at HEAD `6217f1ce603c`, 2026-09-16, verdicts captured
with exit codes:

- 10/10 runs PASS across the five scripts in default mode and with
  `--rev HEAD`, identical byte counts and pinned shas across modes
  (rect-batch 5848, blit 6848, blur-rect 6544, shadow-rect 5136,
  glass-material 20688 bytes).
- Fail-closed: `--rev deadbeef...` and `--rev HEAD~999999` -> ERROR exit 2.
- Tool-axis rot injection: working-copy `spirv-to-spl-words.shs` sabotaged
  to exit 2 -> `--rev HEAD` still PASSes (scan reads the rev-archived tool);
  the same script rotted to point the tool back at the checkout ->
  `ERROR — ... (transcription failed: SABOTAGE)` exit 2. Same shape for
  blit's extractor (`GLSL extraction failed: SABOTAGE`). Both discriminate.
- Dispatcher byte-match: 62 manifest keys vs 62 arms, `comm -23` empty; the
  five converted rows resolve to their new `ref` arms.
  `check-push-must-pass.shs --self-test` -> `PASS — 20 ledger fixtures
  checked`.
- `check-guard-wiring.shs` keeps the five spirv scripts wired; its red (3
  NEW unwired `check-simple-browser-production-*` guards, untracked files
  from another lane) predates this change.

Still open — the class is NOT closed:

- **35 advisory `tree` rows remain.** Most have committed-content subjects
  and are convertible by this same materialisation pattern when picked up;
  per-row plans live in the census work list
  (`push_gate_tree_mode_row_census_2026-09-06.md`).
- **The generic mechanism question is untouched:** what should a `tree` row
  whose subject has no committed form (needs a built artifact, a seed
  binary, or a host tool like `cygpath`) evaluate, and how is it prevented
  from silently scanning the shared checkout? Candidates: materialise the
  rev and run there with a declared missing-tool verdict, or keep `tree`
  with the row's host-scoped subject stated in its header and manifest
  description. Rows in this bucket include `push-dual-run-shadow`,
  `push-plan-acceptance-swept`, `push-entry-closure-ratchet`,
  `push-ui-slim-closure*`, `push-stage4-dynamic-runtime-lane`, and the
  cygpath exec halves of the `push-shs-*` rows. Blocked-on-a-binary is a
  blocker, not a justification — same as recorded 2026-09-07.
- The bypass condition recorded in this file still bounds all of it: topic
  pushes are made with `--no-verify` while blocking gates are red on main,
  so these gates read the right tree only when they run.

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
