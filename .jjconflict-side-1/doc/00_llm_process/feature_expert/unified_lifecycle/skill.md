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

## Current baseline

The observe-only agent base was delivered on public `main` at
`5cd33eca7717a7b87856a001fdb4f72deacfe00d`. The user explicitly waived
verification for that push because the available CLI was a bootstrap seed.
Represent this as `delivered_unverified`, never as `verified`, `approved`, or a
gate receipt.

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
