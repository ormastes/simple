# devhub (dev-tool facades) Feature Expert

## Role

Maintain feature-specific process knowledge for **devhub** — the CLI that gives an
LLM agent famous-CLI ergonomics (gh, mc, Gmail) over whichever backend is actually
configured (Jira/GitHub, GitHub/Bitbucket, Confluence/GH-wiki, MinIO/S3,
Gmail/MS-Graph). Use this skill when work touches `src/app/devhub/` or its specs,
and keep it current as the pipeline produces new artifacts.

## Pipeline Links

Invoke as slash-commands (`/research`, `/design`, …); sources live in `.claude/skills/`:
[research](../../../../.claude/skills/research.md) ·
[design](../../../../.claude/skills/design.md) ·
[impl](../../../../.claude/skills/impl.md) ·
[verify](../../../../.claude/skills/verify.md) ·
[release](../../../../.claude/skills/release.md) ·
[spipe](../../../../.claude/skills/spipe.md) (spec-writing landmines)

## Feature Links

- [Source](../../../../src/app/devhub/) — `main.spl` dispatch; `cmd_*.spl` per facade;
  `adapter_*.spl` per backend; `config.spl` (`ItfConfig`), `errors.spl`, `output.spl`, `retry.spl`
- Launchers: `bin/devhub` (primary), `bin/itf` (compat wrapper), plus `bin/jira`, `bin/bug`
- [Design: overview + decisions D1–D8 + gap registry](../../../05_design/app/devhub/devhub_overview.md)
- [Design: tasks/git/wiki facades](../../../05_design/app/devhub/facade_tasks_git_wiki.md) /
  [storage](../../../05_design/app/devhub/facade_storage.md) /
  [email](../../../05_design/app/devhub/facade_email.md) (Gmail-operator translation tables)
- [User guide](../../../07_guide/app/devhub.md)
- [Unit specs](../../../../test/01_unit/app/devhub/) — 23 spec files; run one at a time
  (`bin/simple test --no-session-daemon <spec>`), verify by `Failed: 0`, never a bare `PASS` line

## Handoff Notes (2026-07-24)

- **Suite re-verified green: 25 spec files, 517 examples, 0 failures** (13 files
  green under `test`; 12 false-fail there with "no parseable pass/fail summary" —
  the known seed-JIT 10–99-example landmine — and are ALL green under the
  authoritative `simple run <spec>`). Verify per-file with `run` when `test`
  reports a summary-less FAIL.
- **Tree landmine (cost a full day): stale untracked `*.smf` stubs shadow real
  modules.** ~9k Feb-dated 179-byte `.smf` stubs under `src/`+`test/` made
  `std.spec` resolve to an empty stub → every spec failed
  `unresolved name: describe` on every binary, mimicking a runner/deploy
  breakage. Fix: quarantine (move out) all untracked `.smf` under `src/` and
  `test/` — they are build artifacts, never git-tracked. Also confirm a
  `simple_seed` sibling exists next to the `simple` binary running `test`
  (frontends delegate SSpec to it; a lone frontend falls back and fails).
- **`errors.spl` `exit_code()` now uses explicit `self.kind`** (was bare `kind`,
  which older evaluators can't resolve — file style is explicit `self.` anyway).

## Handoff Notes (2026-07-20)

- **Five facades shipped, suite green (23/23 files).** Backend selection is always
  explicit `--backend` flag > per-facade config default > error listing configured
  backends — never a silent guess (D1). Search strings pass through to the backend
  untranslated (JQL, gh syntax); **email is the exception** — Gmail operators are
  translated per backend (X-GM-RAW / IMAP SEARCH / Graph KQL).
- **Offline-only test discipline.** Every spec uses PATH-prepended fake binaries or
  pure-function fixtures; no spec may contact a real Jira/GitHub/S3/mail host.
- **Honesty signals are part of the contract:** bb pagination caps at 10 pages and
  says so in human output *and* as `_capped: true` in `--json`; per-backend
  capability gaps raise real errors instead of pretending.
- **Bugs found by construction, not by review** — two mock-stdlib defects (wiki
  Confluence edit, `storage cp` upload) shipped green specs while moving placeholder
  text. Any real-IO path must use `std.io_runtime`/`rt_file_*`, never
  `std.nogc_sync_mut.file_system.file_ops` (a mock). Assert content round-trip.
- **Compiler-level landmines hit repeatedly here** (all filed; see the spec-source
  landmine section of `.claude/skills/spipe.md` before writing fixtures):
  `match` on a bare `val`-constant identifier is an irrefutable capture; `}}`
  collapses inside string literals; `{name}` in a literal parses as interpolation;
  `.split(sep, N)` ignores `N` on the live seed.
- **Tracked next steps:** `rt_is_tty` extern (needs bootstrap rebuild) for the
  non-tty color gap and caret TUI restore; seed redeploy to activate the dormant
  `.split` splitn fix; storage `ls -r` recursive prefix listing.

## Update Rule

After research, requirements, architecture, design, implementation, verification, or
release work changes this feature area, add or refresh links here BEFORE committing,
so the next agent starts from the current project state.

Structure mirrors the sibling entries under `doc/00_llm_process/feature_expert/`.
