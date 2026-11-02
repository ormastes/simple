---
name: debug
description: Diagnose and repair Simple compiler, bootstrap, build or executable failures using real artifacts, independent failure collection and focused regressions.
---

# Debug

Bug fix claims (see `doc/07_guide/infra/tracking/bug_fix_claims.md`): run `sh scripts/check/bug-claim.shs reap` before triage; request bug details with `show <bug_id> --intent for_fixing --session <id>` when you intend to fix (claims it atomically; exit 3 = held by another live session, pick another bug) or `--intent not_for_fixing` otherwise (read-only); heartbeat at least every 2 h (`heartbeat <bug_id> <session>`); finish with `done <bug_id> <session> <pr>` after the PR merges or `release <bug_id> <session>`; never fix a bug whose status is `fixing` under another session.

Read the [shared build collection policy](../../../doc/07_guide/tooling/bootstrap_failure_collection.md)
for continuation, diagnostic exceptions and finite repair budgets.

- Identify the actual producer, source revision, runtime, toolchain and first
  failing boundary. Preserve failed commands, logs, exit status and artifacts;
  a generic label is not proof of its root cause.
- Finish independently runnable modules/tests and group failures by cause.
  Delegate independent repairs to agents with explicit file/cache ownership;
  keep performance and correctness changes separate when requested.
- Reproduce the smallest real failing operation, repair its owner, and execute
  a meaningful regression. Reuse unchanged green evidence and compatible caches.
- Apply an already authorized diagnostic checker exception only in a separate
  recorded attempt with resource/progress monitoring. Keep failures visible and
  restore normal checks before admission or release.
- A new compiler must compile Hello World and run its output successfully before
  its dependent provisional phase. A linked binary alone is not sufficient.
- Stop a cause's repair loop at its declared budget; continue independent work.
  Report unresolved causes and exact resume inputs rather than repeating the
  same failing command or claiming completion from missing tests.

For LLVM boundaries use [LLVM debugging](../../../doc/07_guide/app/llm/llm_bootstrap_llvm_debugging.md).
For unstable native builds use [cache-preserving repairs](../../../.codex/skills/unstable-build-fixes/SKILL.md).
