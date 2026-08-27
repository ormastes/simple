# Domain Research: Release Process Hardening

**Date:** 2026-08-26

**Status:** Complete companion index

The full domain comparison and source list is
[`doc/01_research/infra/release/simple_spipe_release_branch_tag_test_repair_bootstrap_scheduling_hardening_2026-08-26.md`](../infra/release/simple_spipe_release_branch_tag_test_repair_bootstrap_scheduling_hardening_2026-08-26.md).

The selected rules combine Git worktree isolation, signed annotated immutable
tags, GitHub rulesets and protected environments, build-once artifact promotion,
artifact attestations, SemVer, keep-going diagnostic discovery, focused repair
closures, and dependency-graph bootstrap scheduling. The implementation rejects
tag rewriting, release rebuilds, silent platform fallback, self-approved
promotion, stale integration evidence, and descendant compiler promotion after
an ancestor loses qualification.

Primary domain sources are Git, GitHub, SemVer, SLSA, reproducible-builds.org,
Bazel, Cargo, Rust bootstrap, and Go bootstrap documentation, linked in the full
audit above.
