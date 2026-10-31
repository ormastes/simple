# devhub specs: extensionless `#!/bin/sh` fake binaries never ran on the Windows seed

Status: RESOLVED in the spec harness (2026-10-31). The seed-side limit below stays OPEN.
Branch: work/devhub-gh-spec-20261031.

## Symptom (before)

On the Phase 1 seed (Windows, `simple.exe run`):

- `test/01_unit/app/devhub/cmd_github_spec.spl`: 13 x `expected false to equal true`,
  1 x `expected 1 to equal 0`.
- `test/01_unit/app/devhub/cmd_tasks_spec.spl`: 20 x `expected false to equal true`,
  1 x `expected 1 to equal 0` (`jira: --reason has no equivalent ...`).

After the nil fix, the github spec was 16/30 and the tasks spec 33/54.

## Cause 1 (fixed): nil from `rt_file_read_text`

The seed returns `Value::Nil` for a missing file (`file_io.rs:622`). The specs
declared the extern `-> text`, which hid that nil, so `.contains` ran on nil.
Fixed by declaring `-> text?` and reading with `?? ""`. Expected values unchanged.

## Cause 2 (fixed in the harness): the seed does not run the shebang shim

The fake `gh`/`acli` are extensionless `#!/bin/sh` scripts. On win32 the seed
resolves a bare command only to `<name>.exe` (`Command::new` appends `.exe`, and
does not try `.cmd` or the bare file). The spawn fails with rc=-1, so the argv
log was never written.

Evidence (`build/probe2.log`, `build/probe3.log`, `build/probe4.log`):

- Bare `gh` with a `gh.cmd` trampoline on PATH ran the REAL gh (see Incident below).
- Absolute path to `gh.cmd` runs the trampoline. Args with spaces, `|`, `"` and
  `--jq '.[] | .x'` arrive unchanged.
- Production `gh_binary()` (`adapter_github.spl:17`) honours `DEVHUB_REAL_GH`, so
  pointing it at the trampoline routes `gh_available()` and all gh calls to the fake.

Fix: shared installer `test/fixtures/devhub/fake_bin.spl`. On Windows it writes
`<name>.cmd` (`sh "%~dp0<name>" %*`) and returns its path. Both specs set
`DEVHUB_REAL_GH` to that path on Windows, and `acli_path` in the fixture config
points at the acli trampoline. A missing fake makes the path non-existent, so the
call fails closed and never reaches the real CLI. Non-Windows keeps the bare-name
PATH lookup. The only non-Windows change is a fail-closed check for a missing
fake, which only changes the failure path.

Verdicts after the fix (caller PATH unchanged, real gh on PATH):

- `cmd_github_spec.spl`: `outcome=OK executed=30 passed=30 failed=0`.
- `cmd_tasks_spec.spl`: `outcome=OK executed=54 passed=54 failed=0`.

## Incident: real gh was reached during probing (not by the specs)

While probing, a bare-name `gh` call ran the real GitHub CLI because the seed
resolved `gh` to the installed `gh.exe` and not to `gh.cmd`. The calls made were
`gh --version`, `gh issue list --json ...` (read-only, network), and `gh pr review -a`.
The `pr review` call hit "no pull requests found for branch
work/devhub-gh-spec-20261031". No mutating call was made. Read-only probes only
after this were run with absolute paths.

The unmodified baseline spec run also reached real gh. Its log contains real
GraphQL errors (`Could not resolve to a Repository`, `no pull requests found`).

## Open: the seed resolves a bare name only to `.exe`

`cmd_jira_spec.spl` had the same limit and is migrated (commit `a75434832c0`).
Its REST fallback hardcoded the bare `curl`, so it now routes through the
`DEVHUB_REAL_CURL` seam (`cmd_jira.spl` `_jira_curl_binary`). Verdict: 12/12.

Other devhub specs that put a fake on PATH by bare name: none remain. Specs that
mention gh/acli/curl/mc only as strings or argv builders install no fake.
`email_cmd_spec.spl` fakes `mail` by path and never sets PATH.
`test/03_system/app/devhub/feature/gh_shim_backend_routing_spec.spl` runs the
real `bin/gh` on purpose, and one scenario (`pr diff 1`) reaches real gh over the
network. It is not migrated and was not run.

Production bare-name callers without a seam, not faked by any spec:
`adapter_bitbucket.spl:284` and `adapter_confluence.spl:135` call `curl`,
`adapter_minio_mc.spl:395` calls `curl`, and `adapter_outlook_curl.spl` uses
`curl_path: "curl"`. A spec that drives these on Windows would reach the system
curl.exe.

Owner fix for the seed (out of scope here): resolve bare commands through PATH
with PATHEXT on win32. This is not required for the harness fix above.
