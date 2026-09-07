# env/process facade bypass: an 80-site backlog behind a guard recorded as a one-line RED

**Date:** 2026-09-06 · **Status:** RECORDED (census, not fixed) · **Measured at:** `a12a19eb775`
(worktree checkout of `origin/main`). No build was run.

## Verdict

`sh scripts/audit/direct-env-runtime-guard.shs`, rc=1, last line verbatim:

```
STATUS: FAIL direct env/process runtime call outside owners
```

## The census

The guard emits one `file:line:source` row per offending site. Counting rows that match
`^(src|test|scripts)/[^ ]*:[0-9]+:`:

```
80 sites
```

Of those, 29 are `extern fn` re-declarations and the remaining 51 are calls. Per symbol:

| symbol | sites |
|---|---|
| `rt_process_run` | 48 |
| `rt_env_get` | 20 |
| `rt_process_kill` | 6 |
| `rt_process_is_alive` | 3 |
| `rt_process_run_bounded` | 2 |
| `rt_process_is_running` | 1 |

Sample coordinates, verbatim from the guard and each verified present at this sha:

```
src/app/cli_debug/_DebugCommands/command_dispatch.spl:8:extern fn rt_process_run(cmd: text, args: [text]) -> (text, text, i64)
src/app/dashboard/framework_policy.spl:195:    val env_bin = rt_env_get("SIMPLE_BINARY") ?? ""
src/app/debug/remote/test/qemu_runner.spl:8:extern fn rt_process_run(cmd: text, args: [text]) -> (text, text, i64)
src/app/debug/remote/test/qemu_runner.spl:93:    val (stdout, stderr, exit_code) = rt_process_run(gcc, ["-nostdlib", "-march=rv32imac", "-mabi=ilp32", "-o", output_path, asm_path])
src/app/editor/editor_path_text_helpers.spl:84:    val browser = if configured.trim() != "" then configured.trim() else: rt_env_get("BROWSER") ?? ""
```

The 29 local `extern fn` re-declarations are the more structural half: each one re-declares
a runtime symbol inside a consumer module rather than importing the facade, which is the
same anti-pattern the SFFI v2 authority audits check for under the name
`local_raw_declarations` / `local_raw_extern_declarations`.

**Count note.** This session was told "84 sites". The measured figure at `a12a19eb775` is
80 offender rows. The discrepancy is not investigated here; a naive `grep -oE 'rt_[a-z_]+'`
over the whole guard output yields 88 because it also counts symbol names appearing in the
guard's own prose and in a `rt_migration_cycle` mention. 80 is the figure this record
stands behind, and the derivation above is stated so it can be re-checked.

## Why this is a new record and not a duplicate

The guard's redness is already known, but only as a single triage row. It is listed in
`scripts/check/guard_wiring_optout.txt:398`:

```
direct-env-runtime-guard.shs  TRIAGED 2026-08-06 batch 3: RED on this plain Linux host (rc=1), needs an owner not an exemption. Last line: STATUS: FAIL direct env/process runtime call outside owners. see doc/08_tracking/bug/guard_wiring_optout_false_exemptions_2026-08-06.md batch 3
```

and appears in that record's batch-3 table (`guard_wiring_optout_false_exemptions_2026-08-06.md:597`)
as a one-line entry citing exactly **one** sample site
(`src/app/web_dashboard/server.spl:38`). That record's purpose was to establish that the
guard is red and unowned; it did not size the debt. Nothing in
`doc/08_tracking/bug/` enumerates the population, and
`grep -c "to_lower_ascii\|rt_phase_profile_record\|should_scan" doc/08_tracking/todo/todo_db.sdn`
= 0 confirms the tracker carries no rows for this class either. Quantifying it is the
contribution here: "RED, needs an owner" and "80 sites across ~6 symbols, 29 of them local
extern re-declarations" are very different pieces of planning information.

The guard is an **audit-tier** guard, not push-tier —
`grep -n "facade" config/check/must_check_gates.sdn` returns nothing and there is no
`direct-env` row in the manifest. It blocks no push. That is why the backlog can grow
silently.

## What was NOT established

- **No ownership assignment and no migration.** The guard's own output ends by noting its
  dry-run mode does not mutate and that "Unsupported or ambiguous sites require manual
  facade selection". Which of the 80 sites the automated migration cycle could handle, and
  which need manual facade choice, was not determined — the guard was run in dry-run only
  and the migration was not invoked.
- **No judgement on the owner allowlist.** The guard's notion of "outside owners" was taken
  as given. Whether some of the 80 sites are legitimately exempt (e.g. the test-harness
  and QEMU-runner sites, which are arguably tooling rather than product) and should be
  added to the owner set rather than migrated is an open question this record does not
  answer.
- **No trend.** The census is a single point at one sha. Whether 80 is growing, flat, or
  shrinking against the 2026-08-06 state is unknown, because that record published no
  count to compare against. A ratchet baseline would fix that and is not proposed here.
