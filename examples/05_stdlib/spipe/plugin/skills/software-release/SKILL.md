---
name: software-release
description: Plan protected stable or prerelease releases through isolated sessions, reviewed beta backports, immutable candidates, and exact promotion.
---

# Protected Software Release

Release contract: isolated-session; reviewed-beta-backport; immutable-candidate; promote-without-rebuild; protected-ref-guard; non-destructive-release-identity.

Use the packaged `doc/00_llm_process/skill_command/command/release.md` as the
semantic authority. Use SPipe planners to validate evidence; they do not grant
permission or mutate a repository.

Never author in the main worktree, update a protected ref directly, rebuild
during promotion, broadly push tags, or move/delete/reuse a published tag.
Main-fix discovery is read-only and requires caller selection before an exact
reviewed beta backport. A release-first fix requires a reviewed isolated
forward port to main.
