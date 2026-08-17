# HIR package-sibling imported-enum surface leak

Status: FIXED
Status re-verified 2026-08-17 by source inspection (triage shard 01).
Severity: P1 bootstrap blocker
Owner: pure-Simple HIR module lowering
Fix owner: `/root` — CLAIMED at `9299ca99288`

## Reproduction

The no-stub x86 Stage 4 full-CLI build reaches 423 HIR declarations and fails
while lowering `compiler.mir_opt.mir_opt.target_family` with unresolved
`GpuBarrierScope`, `GpuAtomicOpKind`, and `VhdlProcessKind`. The attributed file
contains none of those names. Removing the optimizer facade's unused MIR type
re-export and rebuilding Stage 3 from admitted Stage 2 does not change the
failure.

Retained evidence:

- Stage 3 refresh log:
  `build/bootstrap-stage4-b1df-cycle1/logs/x86_64-unknown-linux-gnu/stage3-refresh-mir-boundary.log`
- Stage 4 log:
  `build/bootstrap-stage4-b1df-cycle1/logs/x86_64-unknown-linux-gnu/stage4-native-build-canonical-mir-boundary.log`
- Refreshed Stage 3 SHA-256:
  `adc4da69b802113f17980b88b783fe7ae6cfc1830ea93b6a660b51c68a2aba91`

## Root cause evidence

`resolve_package_sibling_symbols` in
`src/compiler/20.hir/hir_lowering/_Items/module_lowering.spl` registers every
direct directory sibling through `register_glob_imported_symbols`. That helper
correctly handles an explicit user glob, but it also expands each surface's
named imports. In directory-package mode this leaks imports used privately by
one sibling into every unrelated sibling.

Leaked enums populate `imported_enums`. `lower_module_enum_definitions` then
lowers every imported enum and recursively resolves all variant payload types,
even when the current child never references that enum. Diagnostics render the
current module filename, which explains the false `target_family.spl`
attribution.

## Required repair

- Give directory-sibling registration a declaration-only path: register the
  sibling's own public declarations and intentional explicit exports, but do
  not expand its private named imports.
- Preserve normal explicit `use`, user glob imports, facade re-exports, alias
  resolution, and the existing depth/cycle guards.
- Add an executable mini-package regression where one sibling privately imports
  an enum with nested payload types, a second sibling uses none of it, and a
  third sibling still resolves a bare public declaration from the first.
- Assert the unrelated sibling lowers without inheriting/rematerializing the
  enum. Use behavioral compiler output or symbol results, not source-text
  assertions.
- Rebuild Stage 3 incrementally, rerun the no-stub Stage 4 build, then run exact
  candidate sanity and essential-tool smoke before deployment.

## Full-graph recurrence (2026-08-03)

The earlier repair correctly stopped a sibling's private named imports and
private globs from leaking. It did not stop the sibling's own public enum body
from being copied into every adjacent module. The x86 Stage 4 build therefore
lowered `BitfieldError` inside unrelated `compiler.backend.backend_port`; its
five variants each carry `Span`, a private dependency of `bitfield.spl`, and
reported five false `unresolved type: Span` diagnostics against backend_port.

Package-sibling enum registration is now declaration-only. Explicit user
imports and globs still materialize enum bodies, while unrelated siblings see
the public enum symbol without recursively lowering its private payload graph.
The existing mini-package regression now includes a public sibling enum with a
private nested payload and proves both paths: no body materialization in the
unrelated sibling, and retained materialization for an explicit glob consumer.

## Explicit-import payload-closure recurrence (2026-08-03)

The sibling declaration-only repair remains valid. The current full-graph
failure is a distinct adjacent path: HIR module 427 of 1,431,
`compiler.mir_opt.mir_opt.var_reassign_analysis`, explicitly imports
`MirInstKind` through `compiler.mir.mir_instructions`, then enum-body lowering
cannot resolve `GpuBarrierScope`, `GpuAtomicOpKind`, or `VhdlProcessKind` from
that enum's payloads.

The retained no-stub run reached this failure after 26 minutes 34 seconds of
Stage 4 HIR work at 22,665,128 KiB maximum RSS. Evidence is under
`/tmp/simple-stage4-b1df.WmYLW6/build/bootstrap-stage4-b1df-cycle1/`:

- `stage4-bitcode-full.log` — complete outer build transcript;
- `logs/x86_64-unknown-linux-gnu/stage4-native-build.log` — exact Stage 4
  compiler diagnostic;
- `progress-bitcode.log` and `bootstrap-build-progress.events` — frontier and
  structured progress.

Optimizer-facade payload exports and local source-import reshuffling were
already disproved as root fixes. A materialized explicit enum import must
register the named type dependency closure of its variants in the defining
module's import context. The repair must retain package-sibling
declaration-only behavior and cover direct, facade, nested, and aliased payload
dependencies without importing unrelated owner symbols.

## Focused reproduction guard result (2026-08-03)

Three bounded setup probes were retained under
`/tmp/simple-stage4-enum-closure3-20260803/build/mini_builds/` and no compiler
source was edited:

- a same-package fixture passed because sibling declaration registration masked
  the missing explicit-import upgrade;
- a corrected cross-package fixture passed under ordinary native-build mode,
  which does not reproduce the Stage 4 streaming/package registration order;
- setting `SIMPLE_BOOTSTRAP_STAGE4=1` on that fixture exited before HIR because
  Stage 4 accepts only `src/app/cli/main.spl` or `src/app/os/main.spl` entries.

The next reproducer must therefore be an executable in-memory HIR probe using
the exact facade/owner/support surfaces, or the cross-package fixture with only
the streaming-surface/native-arena controls and without the Stage 4 entry
guard. Do not repeat the three setups above.

Correctness review also identified an independent materialization hazard:
`register_imported_symbol` currently materializes an enum only inside
`if not already_bound`. A package-sibling declaration-only registration can
bind the symbol first, so a later explicit import must be able to upgrade that
binding exactly once when `materialize_enum=true`. The upgrade must remain
dependency-only, reject a conflicting existing owner, and preserve the sibling
path's `materialize_enum=false` behavior.

## Focused repair evidence (2026-08-03)

The pure-Simple repair is on `origin/main` at `f485c7dfe3e` (implementation)
with the direct parser dependency matrix at `b400305d712`. It now:

- extracts named dependencies from every retained `TypeKind` and all three
  `VariantKind` forms through typed owner-local helpers;
- upgrades declaration-only enum bindings independently of initial symbol
  creation, then closes over bounds, defaults, variants, aliases, and facade
  re-exports with physical `(module, item, kind)` identities;
- terminates alias/enum recursion, skips local type parameters, resets closure
  state per lowered module, and fails closed on conflicting or non-type lexical
  bindings; and
- keeps unrelated owner imports absent.

The admitted pure Stage 3 compiler
`62132c47fe04cac8fd9ddfda6d2a57b77995071a9631648350824957ade3cf61`
built the exact in-memory HIR probe with 4 compiled, 131 cached, and 0 failed
modules. The executable returned the expected hard-exit code 30 in 0.01 s.
Build wall time was 20.17 s with 172,288 KiB peak RSS. Static follow-up review
added alias first-write guarding, per-module reset, stronger non-leak checks,
and non-type collision rejection without a fourth runtime cycle, honoring the
three-cycle cap. The full x86 Stage 4 graph remains the final closure proof.

## Current verification status (2026-08-17)

The implementation and regression matrix remain present on current main. The
exact hard-exit probe
`test/03_system/native/hir_materialized_enum_payload_dependencies.spl` covers
declaration-only prebinding followed by explicit facade materialization,
owner-private payload closure, generic bounds/defaults, unrelated-symbol
exclusion, and conflicting terminal identity. The adjacent
`hir_package_sibling_enum_declaration_only.spl` probe preserves the original
package-sibling non-leak invariant while proving an explicit glob still
materializes the enum.

One fresh focused replay was attempted with the canonical
`bin/release/simple` wrapper. It stopped before compilation because the
deployed runtime identity probe could not find a valid
`release/x86_64-unknown-linux-gnu/simple` target. No second replay was made.
The row is therefore `fix-implemented-verification-pending`, not `fixed`, until
an admitted pure-Simple runner repeats the focused hard-exit checks and the
full Stage 4 graph crosses the former HIR frontier.
