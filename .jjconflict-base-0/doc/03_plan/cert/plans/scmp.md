# Software Configuration Management Plan (SCMP)

Companion to `psac.md`/`sdp.md`/`svp.md` (DO-178C §11.4, §7). Target grade:
aero-d/auto-a nearest-achievable, assessed against aero-a for gap visibility.

## Purpose

Define how software life-cycle data is identified, controlled, tracked, and baselined so
any certified configuration can be exactly reconstructed and its change history audited
(DO-178C §7.1 objectives).

## Configuration identification

- **VCS:** jj (Jujutsu) colocated with git, per `.claude/rules/vcs.md`. Every life-cycle
  data item (source, tests, docs, plans) lives in the one repo tree.
- **Configuration item id = commit id.** The jj/git commit id is the authoritative CI
  identifier; there are no separate per-file version numbers. A configuration is fully
  named by a single commit id (the whole tree is snapshotted atomically).
- **Directory-contract identification:** the `FILE.md` manifest system
  (`.claude/rules/structure.md`; root `FILE.md` links child manifests via
  `## Child Manifests`) declares the allowed entries per directory, enforced by
  `scripts/check-workspace-root-guard.shs` (lint + pre-commit hook). This makes "what
  files legitimately belong in this configuration" itself a checked, versioned artifact,
  not tribal knowledge.
- **Auto-generated vs authored items:** derived items (`doc/06_spec/`,
  `doc/08_tracking/*`, `doc/10_metrics/*`, `doc/02_requirements/feature/*`) are marked
  DO-NOT-refactor and regenerated from source; they are identified as *outputs* of a
  configuration, not independently versioned inputs.

## Baseline model: NEVER branch — work on main

- Per `CLAUDE.md` and `.claude/rules/vcs.md`: **never create branches; all work lands on
  `main`.** The baseline is therefore linear — `main` is the single moving baseline and
  any commit id on it is a reproducible point-in-time configuration.
- Rationale for certification: a linear single-line history removes the merge-reconcile
  ambiguity that complicates CM baselining; there is exactly one ancestry chain to audit,
  and "the certified build" is one commit id, not a branch/merge graph to disentangle.
- Consequence (also a gap, see below): there is no formal *frozen* baseline distinct from
  the moving tip — baselines today are implicit (a chosen commit id), not tagged/immutable
  CM baselines with a change-control boundary.

## Change control

- **Pre-commit hook** (`scripts/hooks/pre-commit`, installed to `.git/hooks/pre-commit`):
  runs the FILE.md workspace-root guard, secret-scanning (`secrets.patterns`,
  `pw_patterns.txt`), and format/lint gates before a change enters the configuration.
- **Pre-push hook** (`scripts/hooks/pre-push`) + the pre-push guards in
  `.claude/rules/vcs.md`: block `.jjconflict-*` trees, leaked conflict markers
  (`git grep -c '^<<<<<<<'` must be 0 in the outgoing range), and stale `.git/index.lock`
  from entering `origin/main`. These are the change-control gates that protect the shared
  baseline from corrupt or conflicted content.
- **Sync guards** (`.claude/rules/vcs.md` § Sync guards must gate push; `sync` skill):
  a destructive-upstream file-count guard runs before/after rebase; push happens only
  after guards report 0/0/empty. This prevents a concurrent-session race from silently
  rewriting the baseline (the exact failure class that motivated regenerating these cert
  docs out-of-repo).
- **Review:** the `code-review` skill is invoked on diffs before merge as the human/LLM
  change-review step. (Not independence-gated at DAL D — see `svp.md`.)
- **Problem-driven change:** `bin/simple bug-add`/`bug-gen` + `doc/08_tracking/bug/*` tie
  changes to reported problems; `doc/TODO.md` (via `bin/simple todo-scan`) tracks pending
  work items. TODO→NOTE downgrades are prohibited (`.claude/rules/code-style.md`) so open
  change items cannot be silently retired.

## Configuration status accounting

- **Change history:** `jj log` / `git log` provides full status accounting — who changed
  what, when, under which commit id, with `--stat` for per-file deltas.
- **Tracking layers:** `doc/08_tracking/{bug,test,todo}/*` (auto-generated: `test_db.sdn`,
  `todo_db.sdn`, `test_result.md`) record the verification/problem status of each
  configuration as of each test run.
- **Metrics:** `doc/10_metrics/*` (coverage, perf, dashboard) record measured status per
  configuration.
- Commit-content durability is a known race hazard (`.claude/rules/vcs.md` § Commit
  Content Durability): status accounting requires verifying `jj log --stat` + a HEAD grep
  after each commit, because a concurrent session can capture the wrong files.

## Baseline / release identification

- **Bootstrap stage identity:** the 3-stage bootstrap (seed → stage2 → stage3) produces a
  fixpoint (stage2==stage3 byte-identical); a release configuration is identified by the
  commit id plus the reproduced stage3 binary hash. Determinism is mechanism-proven
  (`238d86c` deterministic entry-shim; build-twice sha256 matches — `cert_roadmap.md`
  Phase 5).
- **Deploy identification:** the shipped tool is `bin/release/<triple>/simple` (e.g.
  `bin/release/x86_64-unknown-linux-gnu/simple`), deployed from a bootstrap-produced
  binary; `bin/simple` symlinks to it.
- **Release-tie:** a release configuration = (commit id, target triple, reproduced binary
  sha256). The Tool Operational Environment pin in `tool_qualification_plan.md` records
  the exact qualified binary/commit/backends for a qualified release.

## Gap to full DAL-D CM

1. **No formal frozen baselines / Change Control Board.** Baselines are implicit commit
   ids on a moving `main`; there is no tagged, immutable, CCB-approved baseline with a
   documented change-approval boundary (DO-178C §7.2.3/§7.2.4).
2. **No archival/retrieval procedure.** There is no documented long-term archive of
   certified configurations + their build environment (compiler nightly, host image) with
   a tested retrieval/reproduction procedure (DO-178C §7.2.7). Determinism makes this
   *feasible* but it is not yet a written, exercised procedure.
3. **No CM records retention policy / load-control / release-record** distinct from the
   git history itself.
4. Reproducibility is proven as a mechanism but **not CI-wired across all targets**
   (`cert_roadmap.md` Phase 5) — a release-time reproducibility gate is still to be added.
