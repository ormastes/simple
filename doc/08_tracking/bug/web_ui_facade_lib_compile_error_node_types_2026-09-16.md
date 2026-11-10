# web_ui facade spec blocked: lib compile error in common/web/node_types.spl

Date: 2026-09-16
Status: SUPERSEDED

## Observed

`web_ui/web_ui_facade_spec.spl` fails before any example runs: loading the
stdlib surfaces `Common mistake detected` at
`src/lib/common/web/node_types.spl:69:5` — the `namespace: text` field
declaration inside `class Element` (likely the reserved-ish `namespace` field
name or a field-shape the checker rejects).

## Impact

Every spec importing the web_ui tree fails at compile time; no web_ui
behaviour can be verified.

## Expectation

`src/lib/common/web/node_types.spl` compiles; `Element` carries its namespace
field (renamed or restructured per language rules).

## Unblock condition

Fix the declaration at node_types.spl:69 (rename the field or adjust to the
sanctioned class-field syntax), then re-run
`test/01_unit/lib/nogc_async_mut/web_ui/web_ui_facade_spec.spl`.


## Triage 2026-11-10 (p3-lib2 lane, work/p3-lib2-20261110)

**Verdict: SUPERSEDED — `node_types.spl` compiles as-is; the unblock condition
is met. Verified with the worktree Rust seed (bin/simple.exe, built 2026-11-10).**

- `./bin/simple.exe test test/01_unit/lib/nogc_async_mut/web_ui/web_ui_facade_spec.spl`
  -> **PASS, rc=0**: `SPEC FILE VERDICT ... outcome=OK declared>=1 executed=1
  passed=1 failed=0`. The spec imports the whole web_ui tree including
  `std.common.web.node_types`; the `namespace: text` field in `class Element`
  (line 69) no longer trips any diagnostic.
- `simple check src/lib/common/web/node_types.spl` surfaces no "Common mistake
  detected" and no namespace-related error (parse/resolve phases clean; the
  command then stops at the environmental "no admitted cached self-hosted check
  worker artifact" gap — no deployed pure-Simple binary in this worktree, same
  as every other check this session).
- MC/DC note: the harness honestly reports "MC/DC: unavailable (compiler lacks
  probe emission)" because the selected binary is the Rust seed — a host-limit,
  not a spec failure; the file's real pass/fail verdict is the PASS above.
- No source change was needed; the file is untouched on this branch.

## 2026-11-11 status — SUPERSEDED (P3-essential library lane, work/p3-lib3-20261111)

Re-verified with this lane's refreshed seed (bin/simple.exe, build-commit
`0791c2b7f4a7`), seed-smoke: `SIMPLE_LIB=src SIMPLE_BINARY=$PWD/bin/simple.exe
$PWD/bin/simple.exe test
test/01_unit/lib/nogc_async_mut/web_ui/web_ui_facade_spec.spl
--mode=interpreter --no-cache` → `SPEC FILE VERDICT ... outcome=OK
declared>=1 executed=1 passed=1 failed=0`, rc=0. `class Element`'s
`namespace: text` field (node_types.spl:69) no longer trips any diagnostic;
the unblock condition is met. The file's last touching merge is PR #7597
(`9e7e7a526edb`); no source change on this branch.
