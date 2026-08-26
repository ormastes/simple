---
name: software-release
description: Prepare and promote stable or prerelease software through isolated sessions, reviewed beta backports, immutable candidates, and exact signed tags.
---

# Protected Software Release

Use `doc/00_llm_process/skill_command/command/release.md` as the canonical process.

Never author in the main worktree, mutate a protected ref directly, build from a release tag, rebuild during promotion, push all tags, or delete/move/reuse a published tag. Beta fixes are explicit reviewed backports of one exact bug-fix commit with provenance and renewed evidence.

Promotion is planning-only until verify reports PASS and a release authority approves the exact admitted candidate. Ask before any external push or publication.
