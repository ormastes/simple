# Stage 4 backend type facade enum payload collision

Status: focused repair verified; full x86 rerun pending
Severity: P1 bootstrap blocker
Owner: pure-Simple compiler backend type facade
Fix owner: `codex/stage4-x86-phase4` in `/home/ormastes/dev/pub/simple-stage4-x86-phase4`
Claimed source revision: `6e9300b345a`

## Exact failure

The final permitted full-resource x86 Stage 4 cycle passed the earlier lint,
DevHub wiki, JSON facade, and TUI terminal blockers. During HIR lowering of
`compiler.backend.backend.compiler`, it failed on two duplicate enum payload
dependencies:

- `compiler.backend.backend_types::CompiledSymbolKind::enum` conflicts with
  `compiler.backend.backend.backend_types::CompiledSymbolKind::enum`.
- `compiler.backend.backend_types::BackendKind::enum` conflicts with
  `compiler.backend.backend.backend_types::BackendKind::enum`.

The build exited 1 after 27m41.98s at 11,417,520 KiB max RSS. It retained the
refreshed Stage 3 compiler with SHA-256
`63de1446a3a5ca95056f35c1ce79653fb8b251d91f713ba80256c4ac9ab2beac`,
but produced no admissible Stage 4 candidate. Essential-tool smoke was not run.

## Owner boundary

`src/compiler/backend/backend_types.spl` declares legacy `BackendKind` and
`CompiledSymbolKind`, then star-reexports
`compiler.backend.backend.backend_types.*`, whose modern backend surface owns
same-named enums. `src/compiler/backend/backend/compiler.spl` imports the
legacy facade with a wildcard, so Stage 4 materializes both physical enum
terminals in one dependency closure.

The next scoped session must narrow or split the facade at the pure-Simple
owner. Do not weaken enum collision detection, add aliases in generated code,
or modify Rust/runtime code.

## Fresh-session repair

The root compatibility facade now explicitly reexports only the three modern
types used by active legacy consumers: `CodegenTarget`, `OptimizationLevel`,
and `CompiledModule`. It no longer reexports the modern `BackendKind`,
`CompiledSymbol`, or `CompiledSymbolKind` physical owners over the same-named
legacy declarations.

Focused fixture:

- `test/03_system/native/stage4_backend_type_facade_contract.spl`
- Exact route: retained focused attempts compile `CompilerBackendImpl` through
  the failing real module and advance beyond both enum collisions.
- Adjacent route: proves facade/direct-owner identity for all three retained
  modern types while retaining the legacy enum owner.

Focused attempt 1 crossed both enum collisions and then failed later because
`backend/env.spl` lacked a named import for its `Backend` field type. That
separate masked closure defect is claimed in
`stage4_backend_env_missing_backend_type_import_2026_08_03.md`; the facade
repair itself produced no collision diagnostic.

Focused attempt 2 also crossed the named `Backend` repair, then stopped later
in `codegen.spl` on separately missing JIT instantiator imports. That isolated
closure gap is recorded in
`stage4_codegen_missing_jit_instantiator_import_2026_08_03.md`; attempt 3 keeps
the executable regression bounded to the facade identity contract.

Focused attempt 3 compiled 223 modules with zero failures and linked the LLVM
core-C-bootstrap fixture in 58.08s at 1,430,848 KiB max RSS. The executable
exited 30 with empty stdout and stderr. The temporary environment import from
attempt 2 was restored because its expanded JIT closure was not independently
green.

Retained focused evidence:

- `build/focused/stage4-backend-facade/compile-attempt1.log`
- `build/focused/stage4-backend-facade/compile-attempt2.log`
- `build/focused/stage4-backend-facade/contract-attempt3.log`
- `build/focused/stage4-backend-facade/contract-attempt3.stdout`
- `build/focused/stage4-backend-facade/contract-attempt3.stderr`

## Required regression evidence

1. A focused real HIR route for `compiler.backend.backend.compiler` resolves
   exactly one physical `BackendKind` and `CompiledSymbolKind` owner.
2. Adjacent consumers of modern `CodegenTarget`, `OptimizationLevel`, and
   payload-bearing `CompiledModule` continue to resolve through the intended
   facade and retain direct-owner type identity.
3. Preserve the existing distinct-enum collision rejection test.
4. Run one full-resource incremental x86 cycle after the focused contract is
   committed; do not repeat an unchanged full command in this scoped session.

## Retained evidence

- `build/bootstrap-stage4-x86-phase4/logs/stage4-cycle3.log`
- `build/bootstrap-stage4-x86-phase4/logs/stage4-cycle3-progress.log`
- `build/bootstrap-stage4-x86-phase4/logs/x86_64-unknown-linux-gnu/stage4-native-build.log`
