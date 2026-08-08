# Stage 4 lint enum terminal collision

Status: claimed
Severity: P1 bootstrap blocker
Owner: pure-Simple HIR materialized payload dependency resolution
Fix owner: `/root` at source revision `4505aec902a`

## Exact failure

The canonical no-stub x86 Stage 4 run loaded 2,116/2,116 sources, retained all
1,431 module surfaces, and completed 43 HIR modules before failing declaration
of `compiler.tools.lint.main`. `LintLevel` and `LintCategory` each report the
same deterministic terminal conflict twice:

- `compiler.tools.lint._LintMain.config_and_model::{item}::enum`
- `lib.nogc_sync_mut.tooling.easy_fix.types::{item}::enum`

The last green module was `compiler.tools.formatter.main`. The command exited 1
after 37m57s at 2,634,216 KiB peak RSS. No Stage 4 candidate was produced.

Retained evidence:

- `/tmp/simple-stage4-bootstrap-4505-20260803/output/logs/x86_64-unknown-linux-gnu/stage4-native-build.log`
- `/tmp/simple-stage4-bootstrap-4505-20260803/progress.log`
- `/tmp/simple-stage4-bootstrap-4505-20260803/output/bootstrap-build-progress.events`

## Prior evidence

`doc/08_tracking/bug/enum_bare_name_collision_enumeration_2026-08-01.tsv`
already classifies the source declarations as duplicated/identical. That static
inventory does not decide whether the correct fix is declaration consolidation,
an explicit adapter, or import-local disambiguation; the compiled HIR reproducer
must decide before source edits.

## Required repair and evidence

1. Trace the exact `compiler.tools.lint.main` import/re-export route and prove
   whether both terminal enums are semantically identical or merely
   name-compatible.
2. Fix the smallest pure-Simple owner. Prefer one canonical shared lint contract
   with explicit adapters over weakening terminal collision checks.
3. Add an exact compiled reproducer for both enums plus an adjacent case where
   same-spelled but genuinely different enum terminals still fail closed.
4. Rerun only the focused failed shard first, rebuild/admit Stage 3 once, then
   resume the canonical Stage 4 cache-backed build within the three-cycle cap.
5. Keep the conflict diagnostic fail-closed; no import reshuffling, local type
   renaming, Rust-seed fallback, stub generation, or source exclusion may be
   accepted as the root fix.
