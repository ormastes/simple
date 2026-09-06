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
- Launchers: `bin/devhub` (primary), `bin/itf` (compat wrapper), plus `bin/jira`, `bin/bug`,
  and **`bin/gh`** — the `gh`-replacement PATH shim (sh; resolves the backend, `exec`s the
  real `gh` for github, routes everything else into `devhub gh`)
- Git routing: `cmd_git.spl` (facade) + `backend_resolve.spl` (one precedence chain, pure
  decision fns) + `gh_compat.spl` (pure gh↔backend argv/JSON translation)
- [Research: CLI wrapper forwarding, normalization, config](../../../01_research/app/tools/devhub/devhub_cli_wrapper_forwarding_2026-09-06.md)
- [Design: overview + decisions D1–D8 + gap registry](../../../05_design/app/devhub/devhub_overview.md)
- [Design: tasks/git/wiki facades](../../../05_design/app/devhub/facade_tasks_git_wiki.md) /
  [storage](../../../05_design/app/devhub/facade_storage.md) /
  [email](../../../05_design/app/devhub/facade_email.md) (Gmail-operator translation tables)
- [User guide](../../../07_guide/app/devhub.md)
- [`gh` shim routing system spec](../../../../test/03_system/app/devhub/feature/gh_shim_backend_routing_spec.spl)
  — runs the real shim as a subprocess; the only place the recursion hazard is exercised
- [Terminal + GUI system spec](../../../../test/03_system/app/devhub/feature/devhub_terminal_ui_spec.spl)
  and [generated manual](../../../06_spec/03_system/app/devhub/feature/devhub_terminal_ui_spec.md)
- [Unit specs](../../../../test/01_unit/app/devhub/) — 23 spec files; run one at a time
  (`bin/simple test --no-session-daemon <spec>`), verify by `Failed: 0`, never a bare `PASS` line

## Handoff Notes (2026-09-06) — devhub finally gets *used*

**The problem was never capability, it was interception.** devhub had 41 files
and working adapters and was bypassed for every single pull request, because
agents type `gh`, `gh` is on `PATH`, and devhub was not in the way. Three
mechanical causes, all now closed:

1. **No backend-neutral git command.** `devhub github` was a pure passthrough to
   the system `gh`; `devhub bb` was a separate command with different flag names
   (`--source`/`--dest` vs `--head`/`--base`). Nothing routed. Now
   `cmd_git.spl` (`devhub gh` / `devhub git`) resolves and routes.
2. **Using devhub cost more than not using it.** `devhub gh pr create` is longer
   than `gh pr create` and added nothing on GitHub. Now `bin/gh` shims `gh`
   itself: same typing, devhub underneath.
3. **`git.default_backend` did not exist** — the design doc named this drift
   under D1 and it sat open. `backend_resolve.spl` now owns one chain:
   `--backend > DEVHUB_GIT_BACKEND > .spipe/config.sdn [devhub] > ~/.config/itf > git remote sniff > error`.

**Traps found the hard way — do not re-learn these:**

- **`bin/gh` on `PATH` is a fork bomb without a guard.** `adapter_github.spl`
  ran `process_run("gh", …)` — a bare name through `PATH`. shim → devhub →
  `gh_run` → shim, forever, ~12 s per cycle. Fixed by the shim exporting
  `DEVHUB_REAL_GH` (absolute path, resolved before it shadows itself) and
  `gh_binary()` preferring it. If you add another adapter that shells to a name
  devhub also shims, it needs the same treatment.
- **`bin/devhub --version` costs 12.0 s** (stdlib read as source per process).
  So the shim resolves the backend *in sh* and `exec`s the real `gh` for the
  github case — **0.078 s**, never entering Simple. Do not "simplify" that
  duplication away; routing every `gh` call through the interpreter makes the
  shim a tax that gets uninstalled.
- **Injecting `--backend` from the shim inverts precedence.** `_extract_flag`
  returns the FIRST match, so the shim's injected copy beat the caller's
  explicit `gh --backend github …`. The backend is handed over as the
  *environment* rung instead. Pinned by a spec.
- **A brace pair in a plain double-quoted Simple string is interpolation.**
  `}}` collapses to `}`, which silently turned a JSON test fixture into invalid
  JSON — four assertions failed on a fixture bug, not a code bug. Compose
  literal braces via helpers (`_lb()`/`_rb()`, as `adapter_bitbucket.spl` has
  always done). `cmd_bb_spec.spl`'s header records the same trap.
- **`.spipe/config.sdn` is git-TRACKED.** Its `devhub:` section therefore holds
  routing facts and the *NAME* of a credential's env var
  (`bitbucket_token_env: BB_TOKEN`), never a secret. `resolve_auth_token`
  resolves `[token_env]` > `[token_cmd]` > `auth.sdn`.
- **`gh pr create --body` had nothing to map onto.** `bb_build_create_pr_body`
  took no description at all, so a PR body would have been silently discarded.
  Added additively (`*_full` / `*_with_body`) so no existing caller or spec
  changed shape.

**Translation policy, and why it is not negotiable:** a gh flag either has an
exact backend equivalent or the command is refused *by name*. Translation
defects are silent — a dropped `--base` opens a PR against the wrong branch and
still exits 0. Everything in `gh_compat.spl` is pure so the whole surface is
testable offline; that is deliberate, keep it that way.

**Five more defects found in review, AFTER the first version passed all its own
tests. Every one of them was invisible to a green suite; read this list before
trusting a passing run here.**

1. **The shim read the wrong repository.** `bin/gh` anchored config and the git
   remote on its own checkout (`REPO_ROOT`), while `find_repo_root()` walks up
   from cwd. A developer with Simple's `bin/` on PATH, standing in a Bitbucket
   repo, got Simple's `git_backend: github`. **The one case the feature exists
   for was the one it broke**, and every test passed because they all ran from
   the Simple root. If you add a scenario here, ask what it holds fixed that
   the real deployment varies.
2. **The refusal policy was a blocklist.** Anything unlisted passed through to
   a backend that never reads it. `gh pr create --body-file` — the form
   `vcs.md` itself prescribes — dropped the entire PR body, exit 0. Now an
   allowlist per verb: declare what you can translate, refuse the rest.
3. **`--json` bypassed the gate entirely.** `_pr_json` ran *before* translation,
   so `--draft --json number` skipped every refusal and would have opened a
   non-draft PR, exit 0. The bypass sat on the **LLM/script path** while the
   human path refused correctly. Translation now runs first for every path;
   `_pr_json` is a renderer, never a gate. Keep that ordering.
4. **Flag scanners inspected VALUES as flags.** A PR body is one argv element of
   arbitrary text; a body starting with `---` (an ordinary markdown rule) was
   refused as an unknown flag, and a body whose text was `--base` got *rewritten*
   to `--dest`. `flag_positions()` + `VALUE_TAKING_FLAGS` fix both. Any new
   `starts_with("--")` scan in this area is a bug until proven otherwise.
5. **`std.nogc_sync_mut.file_system.file_ops` is a MOCK.**
   `file_exists("/nonexistent")` -> **true**; the reader returns
   `Some("mock file content: " + path)` and leaks the `Option` into text. Use
   `app.io.mod.{file_read, file_exists}`, verified honest. `config.spl` reads
   auth material through the mock's names and works only by import-closure
   resolution luck. Filed:
   `doc/08_tracking/bug/file_ops_mock_answers_for_nonexistent_paths_2026-09-06.md`.

**Method note worth keeping:** each of these was found by *running the thing on
realistic input*, not by reading it — probing `file_exists` instead of assuming,
running a control test to prove `to_not_contain` actually discriminates, timing
the shim again after adding a loop, and diffing a clean `git worktree` at HEAD
before attributing test failures to the change.

**Evidence (2026-09-06):** `gh_compat_spec.spl` 29/29, `backend_resolve_spec.spl`
22/22, `gh_shim_backend_routing_spec.spl` 8/8 (runs the real shim as a
subprocess, including the PATH-shadowed configuration where recursion is live).
devhub unit suite: 29 failures at HEAD → 28 with this change, +51 new passing
examples, no new failures. The remaining failures are pre-existing and
environmental (unauthenticated `gh`, `ItfError` exit codes, auth round-trip) —
verified identical in a clean `git worktree` at HEAD before claiming that.

**Deliberately not built:** `bin/mc` / `bin/jira` shims (same pattern, no
demonstrated bypass yet), a GitLab backend, and gh-shaped JSON for
`approve`/`comment`/`status`. Recorded as todos, not scaffolded.

## Handoff Notes (2026-07-24)

- **Suite re-verified green: 25 spec files, 517 examples, 0 failures** (13 files
  green under `test`; 12 false-fail there with "no parseable pass/fail summary" —
  the known seed-JIT 10–99-example landmine — and are ALL green under the
  authoritative `simple run <spec>`). Verify per-file with `run` when `test`
  reports a summary-less FAIL.
- **Terminal and desktop launch are covered by 9 modern SSpec scenarios.**
  `bin/devhub --gui` hosts a loopback page and opens the repo-managed Electron
  shell by default (`--browser` is the explicit fallback). The page consumes the
  generated `fluid_light` SimpleOS snapshot: the registered Fluid OS package
  sourced from `config/themes/raw/fluid_os/DESIGN.md`. Visual evidence is stored
  beside the generated system manual.
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
