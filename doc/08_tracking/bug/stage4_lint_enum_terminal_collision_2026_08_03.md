# Stage 4 lint enum terminal collision

Status: fix implemented — focused native and full Stage 4 replay pending
Severity: P1 bootstrap blocker
Owner: pure-Simple lint contract ownership
Fix owner: `/root/priority_lint_enum` at source revision `1a2fd808fc`

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

## Implemented repair (2026-08-17)

The declarations are semantically identical: both enums have the same variant
sets and the lint model already imports `LintLevel` from
`std.tooling.easy_fix.types`. The same import also named `LintCategory`, but a
stale local `LintCategory` declaration shadowed it. The smallest canonical fix
deletes that one duplicate declaration, leaving the public lint facade to
re-export both physical enum terminals from the shared easy-fix contract.

`test/03_system/native/lint_enum_terminal_canonical_owner.spl` is the exact
compiled entry-closure regression: it imports both enums through both public
routes under their original spellings. The adjacent fail-closed guard is the
same-spelled/different-terminal branch in
`test/03_system/native/hir_materialized_enum_payload_dependencies.spl`.

The one permitted focused replay was attempted before editing, but the deployed
wrapper rejected its missing release target during the bounded identity probe,
before compiler startup. Consequently this record remains verification-pending;
neither focused native success nor a resumed canonical Stage 4 build is claimed.
