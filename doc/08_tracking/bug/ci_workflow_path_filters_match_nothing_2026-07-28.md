# CI workflow `paths:` filters matched nothing (fail-open dormant workflows)

- **Status:** fixed for 9 workflows; 1 residual (`index-validate.yml`) OPEN
- **Found:** 2026-07-28
- **Scope:** `.github/workflows/**`

## Class of defect

A GitHub Actions `paths:` filter that matches no file in the repository means the
workflow **never triggers**. It reports no failures, which is visually
indistinguishable from "passing". Any green CI history for an affected workflow
during its dormant window is meaningless.

Detected by resolving each `paths:` / `paths-ignore:` glob (GitHub semantics:
`*` does not cross `/`, `**` does) against `git ls-files` — 107,989 tracked
files — rather than eyeballing.

## Fixed (commit landing 2026-07-28)

| Workflow | Broken filter | Meant to gate | Repointed to |
|---|---|---|---|
| `electron-tests.yml` | `scripts/check-electron-live-smoke.shs` | Electron live smoke script | `scripts/check/check-electron-live-smoke.shs` |
| `simpleos-build.yml` | `scripts/os_qemu_test.shs` | SimpleOS QEMU test script | no successor in repo — entry removed (`scripts/os/**` still gates) |
| `core-mcp-dev-pipeline.yml` | `scripts/deploy-marketplaces.shs` | marketplace deploy script | no successor in repo — entry removed |
| `dashboard-ci.yml` | `src/lib/std/src/tooling/dashboard/**` | dashboard stdlib tooling | `src/compiler_rust/lib/std/src/tooling/dashboard/**` |
| `gui-hardening-evidence.yml` | `test/baselines/html_compat/**`, `test/baselines/famous_site_corpus/**` | GUI baselines | `test/baselines/` does not exist at all — entries removed (`test/fixtures/famous_site_corpus/**`, 133 files, still gates) |
| `rust-bootstrap-multiplatform.yml` | `.github/workflows/{cross-platform,simple-llvm-cross,test-isolation,windows-tests}.yml` | 4 consolidated-away workflows | entries removed |
| `simple-strict-lints.yml` | `test/code_quality/**` | code-quality lint specs | `test/03_system/quality/code_quality/**` (21 files) |
| `vscode-tests.yml` | `test/unit/app/vscode_extension/**` | vscode extension tests | `test/03_system/app/vscode_extension/**` + `test/system/app/vscode_extension/**` |
| `vhdl-tests.yml` | `src/compiler/backend/vhdl/**`, `src/compiler/backend/vhdl_*.spl`, `src/compiler/vhdl_constraints.spl`, `examples/vhdl/**` | VHDL backend + golden VHDL | `src/compiler/70.backend/backend/vhdl/**`, `src/compiler/70.backend/backend/vhdl_*.spl`, `src/compiler/70.backend/vhdl_constraints.spl`, `examples/09_embedded/vhdl/**` |

`vhdl-tests.yml` was the worst case: **every** `pull_request.paths` entry was
dead, so the PR lane was 100% dormant. Its run steps also `cd
examples/vhdl/golden` (gone); repointed at `examples/09_embedded/vhdl` with the
real entities (`counter`, `alu`, `fsm`, `adder` — `traffic_light` no longer
exists).

## Dormant window — dating limitation

The local clone is **shallow** (`.git/shallow` present, graft at 2026-07-01,
6,552 commits). None of the stale paths above appear anywhere in the available
history, and the 2026-07-25 commit `37cda4befdc` ("restore main from pushed jj
conflict tree") re-added the whole tree, further flattening rename history.

Therefore the provable bound is: **every filter above has matched nothing for at
least the 27 days 2026-07-01 → 2026-07-28, and almost certainly longer.** An
exact start date requires `git fetch --unshallow`. Treat all green runs of these
workflows in that window as vacuous.

## OPEN residual: `index-validate.yml`

`on.pull_request.paths` is `index/**` only — the sole filter, matching nothing,
so the workflow is 100% dormant. Its header declares it a *template* "For the
simple-lang/registry repo", and its job steps invoke
`src/tools/validate_index_entry.spl`, `src/tools/verify_oci_refs.spl`,
`src/tools/check_duplicates.spl` — **none of which exist in this repo either**.

Not repaired: removing `index/**` would make it run on every PR and fail; there
is no successor path to repoint at; deleting a workflow to simplify is out of
scope. Decide explicitly whether to move it to the registry repo or delete it.

## Follow-up

Add a lint/pre-push check that resolves every workflow `paths:` glob against
`git ls-files` and fails on a zero-match entry, so this cannot regress. Note
`bin/simple lint` cannot serve here (fail-open on syntax errors per
`lint_does_not_detect_syntax_errors_2026-07-28.md`, and does not read YAML).

## Re-verification and re-fix 2026-11-25 (P3 fleet, release/1.0.0)

The 2026-09 tree transplant (88aac2ffe28) resurrected pre-fix revisions of the
workflow files, so most "Fixed" rows above were live again on release/1.0.0.
Re-verified every `paths:` entry against `git ls-files` (GitHub glob semantics)
and re-applied the documented fixes:

- `electron-tests.yml`: `scripts/check-electron-live-smoke.shs` (DEAD) →
  `scripts/check/check-electron-live-smoke.shs` (ALIVE), push + PR lanes.
- `core-mcp-dev-pipeline.yml`: removed `scripts/deploy-marketplaces.shs`
  (DEAD, no successor), push + PR lanes.
- `dashboard-ci.yml`: `src/lib/std/src/tooling/dashboard/**` (DEAD) →
  `src/compiler_rust/lib/std/src/tooling/dashboard/**` (ALIVE), both lanes.
- `gui-hardening-evidence.yml`: removed `test/baselines/html_compat/**` and
  `test/baselines/famous_site_corpus/**` (both DEAD; `test/baselines/` does
  not exist). Additionally found and fixed a same-class dead entry not in the
  original table: `scripts/check-gui-hardening-open-gates.shs` (DEAD) →
  `scripts/check/check-gui-hardening-open-gates.shs` (ALIVE), including the
  run step that invoked the old path.
- `vscode-tests.yml`: `test/unit/app/vscode_extension/**` (DEAD, 0 tracked
  files) → `test/03_system/app/vscode_extension/**` (ALIVE), both lanes; the
  guarded "Simple-side unit tests" step now points at the same live dir.
  (`test/system/app/vscode_extension/**` from the original fix is itself dead
  in the current tree, so it was not re-added.)
- `vhdl-tests.yml`: all PR-lane entries were dead again. Repointed to
  `src/compiler/70.backend/backend/vhdl/**`,
  `src/compiler/70.backend/backend/vhdl_*.spl`,
  `src/compiler/70.backend/vhdl_constraints.spl`,
  `examples/09_embedded/vhdl/**`. Run steps now `cd examples/09_embedded/vhdl`
  and analyze all `*.vhd` recursively (golden files live under
  `builder/golden/` and `backend/golden/`); elaboration targets verified
  against the actual `entity` declarations: `counter`, `alu`, `traffic_light`
  (declared in `fsm.vhd`), `adder`.
- `simpleos-build.yml` and `simple-strict-lints.yml`: the 2026-07-28 fixes
  survived the transplant (verified ALIVE); no change needed.
- `rust-bootstrap-multiplatform.yml`: the four absent-workflow entries are now
  an intentional tripwire with an in-file comment ("These workflows must
  remain absent; trigger this guard if someone restores one"); left as-is.
- Residual `index-validate.yml`: the file no longer exists in the tree, so the
  OPEN residual is moot.

After-evidence: every `paths:` entry in the six touched workflows resolves to
≥1 tracked file via `git ls-files` (checked 2026-11-25); YAML structure
validated line-wise (no tabs, balanced edits). The follow-up zero-match lint
from the original report remains a good idea and is still not implemented.

**Status:** RESOLVED 2026-11-25 (re-fixed after tree transplant; residual
index-validate.yml gone).
