# dashboard app CLI is a no-op stub; `dashboard_log_modes_spec.spl` tests removed functionality

**Date:** 2026-07-20
**Component:** `src/app/dashboard/main.spl`
**Severity:** Medium — not an interpreter/compiler defect; a product-level
gap between an intentionally-stubbed app and a spec that was never updated
to match
**Found by:** whole-suite triage campaign, `test/02_integration/app/`
cluster

## Symptom

`test/02_integration/app/dashboard_log_modes_spec.spl` spawns
`bin/simple run src/app/dashboard/main.spl <args>` as a subprocess and
asserts CLI behavior (`--help` text, `--log-mode=json` output,
`--progress=dot` rendering, exit-code-1 on an invalid `--log-mode`, JSON
error envelope for unknown commands). All 5 examples fail with empty
stdout and (for the "rejects invalid log mode" case) exit code 0 instead
of the expected 1.

Root cause, confirmed by reading the source directly (not a compiler bug):

```simple
fn _dashboard_surface_result(args: [text]) -> text:
    "status=migrated target=simple-ide args=" + args.join(" ")

fn main() -> i64:
    0
```

`src/app/dashboard/main.spl` is a 14-line placeholder. `main()` takes no
arguments and unconditionally returns `0` — there is no CLI arg parsing, no
`--help`/`--log-mode`/`--progress` handling, nothing. The
`_dashboard_surface_result`/`_run_serve_result`/`_run_gui_result`/
`_run_agents_result` helper functions that do exist all just format a
`"status=migrated target=simple-ide ..."` string and are unused by `main()`
— they read as leftover scaffolding from a migration of the dashboard
surface to `simple-ide`, with the stub left behind as a compatibility
placeholder rather than a working CLI.

## Comparison with sibling `*_log_modes_spec.spl` targets

Checked the other apps this campaign's `*_log_modes_spec.spl` files target
(`app_root` → `src/app/main.spl`, `cli`, `env`, `exp`, `mcpgdb`, `play`,
`plugin`, `qualify_ignore`, `replay`) — all have substantial (100+ line)
`main()` implementations with real argument handling. `dashboard` is the
only one reduced to a stub. This is **not** a shared root cause across the
`*_log_modes_spec.spl` family (an earlier hypothesis); it's specific to
this one app.

## Recommended direction (not attempted here — product decision, not a
mechanical fix)

Either (a) restore `--help`/`--log-mode`/`--progress` CLI handling in
`dashboard/main.spl` matching the contract the spec expects, or (b) if the
dashboard surface is genuinely fully migrated to `simple-ide` and the CLI
entrypoint is intentionally dead, retarget or delete
`dashboard_log_modes_spec.spl` and its underlying `--log-mode` contract
expectations. Left the spec file unmodified per the "never rewrite an
assertion to force green" rule — deciding which of these two paths is
correct requires product/ownership context beyond this triage pass.
