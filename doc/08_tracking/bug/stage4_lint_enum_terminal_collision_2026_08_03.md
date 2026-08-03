# Stage 4 lint enum terminal collision

Status: repaired; Stage 4 cycle 2 validation pending
Severity: P1 bootstrap blocker
Owner: pure-Simple HIR materialized payload dependency resolution and lint contract ownership
Fix owner: `codex/stage4-x86-phase4` in `/home/ormastes/dev/pub/simple-stage4-x86-phase4`
Claimed source revision: `1221d92684d`

## Exact failure

The strict cache-backed Linux x86_64 Stage 4 cycle loaded 2,116/2,116 sources,
retained and released all 1,431 module surfaces, then failed before completing
the first HIR module while lowering `compiler.tools.lint.main`. `LintLevel` and
`LintCategory` each reported the same deterministic terminal conflict twice:

- `compiler.tools.lint._LintMain.config_and_model::{item}::enum`
- `lib.nogc_sync_mut.tooling.easy_fix.types::{item}::enum`

The full wrapper exited 1 after 19m16.55s. `/usr/bin/time` recorded 2,126,936
KiB max RSS; the progress watcher recorded 2,089,300 KiB peak tree RSS. No
Stage 4 candidate or deployment exists.

Retained evidence:

- `build/bootstrap-stage4-x86-phase4/logs/stage4-cycle1.log`
- `build/bootstrap-stage4-x86-phase4/logs/stage4-cycle1-progress.log`
- `build/bootstrap-stage4-x86-phase4/logs/x86_64-unknown-linux-gnu/stage4-native-build.log`
- `build/bootstrap-stage4-x86-phase4/bootstrap-build-progress.events`

## Boundary decision

Both definitions had the same ordered variants and no conversion or independent
serialization contract. `std.tooling.easy_fix.types` now owns `LintLevel` and
`LintCategory`; `compiler.tools.lint.main` explicitly re-exports those exact
identities. Compiler-local `Lint` and `LintResult` remain in place because their
constructor API differs from the shared classes. All lint submodules now import
only the EasyFix symbols they use, preventing the distinct local/shared model
classes from colliding through wildcards. The strict terminal-identity check is
unchanged.

## Required regression evidence

1. An exact compiled reproducer covers both real lint enums and their import or
   re-export route.
2. An adjacent same-terminal alias/re-export case succeeds.
3. An adjacent same-spelled but genuinely different enum-terminal case remains
   fail-closed with the terminal identities in its diagnostic.
4. Only the focused failed shard runs before the admitted Stage 3 refresh and
   the second cache-backed Stage 4 cycle.

Focused evidence:

- `hir_materialized_enum_payload_dependencies.spl` compiled 135 modules and
  exited 30. It proves a same-terminal enum facade/direct-owner route succeeds,
  a distinct same-spelled enum owner fails with both terminal identities, and
  the first binding remains selected.
- `stage4_lint_shared_enum_contract.spl` imported both real public routes. It
  compiled but exited 70 before the repair, then compiled and exited 30 after
  the repair.
- Logs are retained under
  `build/focused/stage4-lint-enum-terminal-collision/`.

## Cycle accounting

- Cycle 1/3: reproduced at `1221d92684d`; no source repair attempted yet.
- Focused repair gate: PASS; full Stage 4 cycle 2/3 is pending.
