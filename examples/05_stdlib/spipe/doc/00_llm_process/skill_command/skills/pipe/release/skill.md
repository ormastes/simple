<!-- generated-from: doc/00_llm_process/skill_command/command/release.md -->
# Protected Software Release

Release contract: isolated-session; reviewed-beta-backport; immutable-candidate; promote-without-rebuild; protected-ref-guard; non-destructive-release-identity.

Use the canonical semantic source at `doc/00_llm_process/skill_command/command/release.md`.

Start one isolated release branch/worktree, read `release/version.sdn`, and require verified evidence. Beta maintenance accepts only explicit reviewed bug-fix backports with exact provenance and renewed post-application evidence. Create an immutable candidate, build once, and promote exact admitted artifacts through one signed annotated exact tag after approval.

Never update protected refs directly, rebuild during promotion, select fixes automatically, push all tags, delete/move/reuse a published tag, or use fallback artifacts. Rollback redeploys a prior admitted release; corrections get a new version.
