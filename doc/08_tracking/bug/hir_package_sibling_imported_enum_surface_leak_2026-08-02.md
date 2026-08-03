# HIR package-sibling imported-enum surface leak

Status: reopened — explicit named enum imports lose payload dependency closure (2026-08-03)
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
