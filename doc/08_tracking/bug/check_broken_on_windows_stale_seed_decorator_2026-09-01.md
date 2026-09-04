# `simple check` broken on Windows: stale seed rejects `@always_inline` in its own stdlib (RESOLVED 2026-09-01 by seed redeploy)

## Status

RESOLVED — no source change was needed; the fix (`is_directive_decorator`
whitelisting `always_inline`, `compiler/src/decorator_apply.rs:61`, comment
dated 2026-08-26) was already at HEAD. The deployed `bin/simple.exe` predated
it. Rebuilt and redeployed 2026-09-01.

## Symptom

Every `bin/simple.exe check <file>` on this Windows host exited 1 with

```
error: semantic: unknown decorator `@always_inline` on function `file_read_nullable`
```

regardless of the input — a clean hello world and a type-broken file produced
byte-identical verdicts. `--version` answered cleanly, which is exactly why the
binary looked healthy. The error is raised while the seed INTERPRETS
`src/app/cli/check_entry.spl`'s import closure (the JIT demotes to the
interpreter on this path — 14 codegen body failures on `ffi` globals), hitting
`@always_inline fn file_read_nullable` in `src/lib/nogc_sync_mut/io_runtime.spl`
before the user's file is ever consulted.

## The SEGV premise: answered, not reproduced

This lane was opened as "`simple check` SEGVs on a three-line hello world;
capture the faulting stack with cdb." **No fault reproduces on this host**: the
failure is a clean rc=1 semantic error, exit status read directly (never
through a pipe), so there is no faulting stack and cdb is not applicable to
this failure mode. The SEGV report matches the Linux stage-binary incident
(`stage3_native_build_and_compile_segv_on_hello_world_2026-08-18.md`), which is
a different artifact class; if a crash surfaces now that the decorator error no
longer masks everything downstream, that is a new record. Post-redeploy runs of
`check` on clean, parse-broken, type-broken, and undefined-variable fixtures
all exited 0 or 1 — no crash observed.

## Root cause

`decorator_apply.rs`'s strict module-level path (line 153 emits exactly this
message) skips names accepted by `is_directive_decorator`. The deployed seed
(md5 `856e49ab0e499f5703f150491065960d`, 2026-08-24, 28,291,570 bytes) was
built before `always_inline`/`force_inline`/`no_reorder` were added to that
whitelist: `strings` finds pre-fix members (`gpu_kernel` x4, `snapshot_test`)
but zero occurrences of the post-fix members, and the message text itself
appears — a pre-2026-08-26 build. A `target/release/simple.exe` dated
2026-09-01 13:18 (md5 `c8f08d98969d6288afe2971cc4d5f21f`) had the SAME defect —
mtime is not provenance.

## Fix / evidence

`cargo build --release --bin simple` in `src/compiler_rust` (2m22s, real
recompile) produced md5 `f9bf124d933a0de0af5d999444234996` (38,700,544 bytes),
which contains the post-fix whitelist literals; `deps/simple.exe` and
`simple.exe` synced (cmp FRESH), deployed to `bin/simple.exe`.

| fixture | before (856e49ab) | after (f9bf124d) |
|---|---|---|
| clean hello world | rc=1 `unknown decorator` | rc=0 `All checks passed (1 file(s))` |
| unbalanced parens | rc=1 `unknown decorator` | rc=1 `[parser_error] line 1:9: expected parameter name` naming the fixture |
| `val x: i64 = "not a number"` | rc=1 `unknown decorator` | rc=0 silent green — SEPARATE structural bug, see below |

## Follow-ups

- `check` reaches a real implementation (`src/app/cli/dispatch/table.spl:156` →
  `src/app/cli/check_entry.spl` → worker `src/app/check/main.spl`) but that
  implementation is parse-only; type errors and undefined variables pass
  silently. Filed:
  `doc/08_tracking/bug/check_silently_passes_type_errors_parse_only_2026-09-01.md`.
- Regression pins:
  `test/01_unit/app/cli/check_clean_file_passes_spec.spl` (clean file passes,
  and the "unknown decorator" stale-seed signature must never reappear) and
  `test/01_unit/app/cli/check_broken_file_reports_error_spec.spl` (broken input
  is reported, not crashed on, not silently passed).
- Cross-platform: no Unix-side code was touched; the change is a Windows seed
  binary redeploy plus two platform-agnostic specs (binary picked by probing
  `bin/simple.exe` then `bin/simple`).
