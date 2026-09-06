# Unified lifecycle feature expert

Canonical research, architecture, design, plan, requirements, guide, and SSpec
use the slug `scv_jj_git_devhub_spipe_unified_lifecycle`.

Preserve these invariants: SCV owns lifecycle identity/evidence; aliases are
non-canonical; approvals/gates bind exact revisions; SJ is the only supported
protected mutation planner/gateway; DevHub exposes typed provider capabilities;
Spipe orchestrates; sync is three-way and field-authoritative; published
releases are immutable; base behavior is observe-only.

Never modify the concurrently developed SCV file-entity identity store as a
shortcut for lifecycle identity. Use `std.scv.lifecycle.*`.

## Research authority

The condensed `doc/01_research/app/tools/scv/scv_jj_git_devhub_spipe_unified_lifecycle_2026-08-25.md`
(165 lines) is a SUMMARY. The full texts are `..._unified_lifecycle_full_2026-08-25.md`
(2,869 lines) and `..._unified_release_review_work_item_2026-08-25.md` (1,630 lines)
in the same directory. The second is the only source for the four SCV tag defects,
release units / monorepo version sets, authority modes A/B/C, and the R0-R4 review
risk classes. Prefer the full texts where they disagree with the summary.

## Trap: `use` is eager, and `bin/sj` is the landing path

`bin/sj` execs `src/app/sj/main.spl` FROM SOURCE, and `scripts/check/land.shs`
invokes `sj`. Simple resolves `use` eagerly, so any import added to `main.spl` is
opened and parsed on every push. Measured by strace 2026-09-05: an `integrate_plan`
import there — referenced only from a `plan` arm that pushes never take — opened
`scv/lifecycle` four times per `bin/sj --help`, putting the entire lifecycle graph
on the critical path of every push on the machine, where one parse error under
`src/lib/scv/lifecycle/**` would have broken pushes for every session.

Never add a lifecycle import to `src/app/sj/main.spl`. Route a new large-import
subcommand to its own entry file and dispatch in `bin/sj` (`plan` ->
`src/app/sj/plan_main.spl` is the worked example). Equally: never intercept
`sj git push` to force a dry-run — that spelling belongs to `land.shs`.

## Current baseline

The observe-only agent base was delivered on public `main` at
`5cd33eca7717a7b87856a001fdb4f72deacfe00d`. The user explicitly waived
verification for that push because the available CLI was a bootstrap seed.
Represent this as `delivered_unverified`, never as `verified`, `approved`, or a
gate receipt.

**Measured 2026-09-05: that base was DORMANT.** Real, unstubbed, zero TODO markers —
and ~20-25% of the 7-stage design, with no producer, no executor, no provider
implementation, and no mutation path. Do not read "the code exists" as "the stage
works": check for a non-test caller before believing any capability claim here.
Stage 0.5 landed items 1, 3 and 4 the same day — `bin/sj plan` reaches the typed
layer, `devhub lifecycle record-change` persists through `lifecycle_store_write`,
and `LocalScvProvider` is the first of five `LifecycleProvider` implementers.
Everything stays diagnostic: 0 of 18 acceptance criteria hold an authoritative
PASS while `bin/simple` is the seed.

When handling a follow-up:

1. Resolve the exact local lifecycle revision and policy digest.
2. Read the plan, guide, and `.spipe/.../state.md` before proposing promotion.
3. Keep ordinary inspection observe-only.
4. Require fresh admitted-CLI evidence before enabling protected mutation,
   provider publication, signed tags, releases, or SCV content authority.
5. Record any explicit no-verify publication as an audit/waiver fact scoped to
   that push. Never infer permission for a later bypass.

Use the typed DevHub/SJ lifecycle surfaces. Do not reproduce Git/JJ/provider
mutation logic inside this skill.
