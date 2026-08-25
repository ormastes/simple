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

