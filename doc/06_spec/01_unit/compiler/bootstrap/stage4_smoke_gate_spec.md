# Stage4 Smoke Gate Specification

| Tests | Active | Skipped | Pending |
|-------|--------|---------|---------|
| 18 | 18 | 0 | 0 |

## Scenarios

### bootstrap stage4 smoke gate

#### keeps diagnostic whole-archive mode out of canonical bootstrap

The canonical bootstrap script rejects the diagnostic whole-archive override.

#### fails bootstrap when the freshly built full CLI cannot execute code

The Stage 4 smoke requires fresh code execution and a specific failure message.

#### gates test lint and duplicate-check on the fresh Stage 4 CLI

The essential-tools gate exercises real pass and fail cases through the fresh
candidate.

#### runs every maintained test surface for release bootstrap

Release bootstrap invokes the maintained whole test surface.

#### rejects seed fallback and gates the full candidate before deployment

The candidate admission helper is sourced and seed fallback remains forbidden.

#### builds and requires the dedicated compiler backfill for a full CLI

The compiler backfill is built before the hosted full-CLI request and stale
backfill reuse is rejected.

#### publishes the Linux LLVM full CLI with its hosted providers

The ordered Linux LLVM workflow builds, stages, and uploads the full CLI plus
the runtime, font, and winit providers before later parity gates. Missing
artifact files fail the upload, and seed binaries are excluded.

#### uses Cargo staticlib names for both Windows toolchains

The bootstrap selects the correct `.lib` or `.a` naming for MSVC and GNU.

#### exports the Stage4 pure driver inputs and requests core C

Stage 4 exports its target, cache, worker, and runtime paths and selects
`core-c-bootstrap`.

#### uses supported runtime bundles for Stage 2 and Stage 3

```simple
val script = rt_file_read_text("scripts/bootstrap/bootstrap-from-scratch.sh") ?? ""
val stage2_pos: i64 = script.find("# Stage 2: seed compiles bootstrap_main.spl") ?? -1
val stage3_pos: i64 = script.find("# Stage 3: stage2 recompiles bootstrap_main.spl") ?? -1
val capability_pos: i64 = script.find("stage2_capability_ok=0") ?? -1
val stage2_block = script.substring(stage2_pos, stage3_pos)
val stage3_block = script.substring(stage3_pos, capability_pos)

expect(stage2_pos).to_be_greater_than(-1)
expect(stage3_pos).to_be_greater_than(stage2_pos)
expect(capability_pos).to_be_greater_than(stage3_pos)
expect(stage2_block).to_contain("--runtime-bundle core-c-bootstrap")
expect(stage3_block).to_contain("--runtime-bundle core-c-bootstrap")
expect(script).to_not_contain("--runtime-bundle rust-hosted")
```

#### resolves a src entry closure before the implicit whole-tree load

Native build resolves the requested source closure without loading the
implicit whole tree first.

#### keeps bootstrap MIR symbol names compatible with the pure frontend

Bootstrap MIR naming preserves qualified imported and same-module symbols.

#### parses comma-separated class mixins in the Stage4 frontend

The parser accepts comma-separated class mixins and records each mixin.

#### consumes optional suffixes after generic types

The parser consumes optional suffixes after generic type expressions.

#### parses fat-arrow match arms with indented statement blocks

Fat-arrow match arms retain indented statement-block parsing.

#### initializes the Engine2D offscreen optional before backend selection

The offscreen Engine2D value is explicitly optional until backend creation
succeeds.

#### preserves public visibility on trait declarations

Trait parsing and code generation preserve public visibility.

#### carries declaration order without calling Dict keys during desugaring

Frontend module assembly records declaration order explicitly and async
desugaring does not depend on dictionary key iteration.

## Operator Summary

Run this focused source contract with:

```sh
SIMPLE_LIB=src bin/simple test test/01_unit/compiler/bootstrap/stage4_smoke_gate_spec.spl --mode=interpreter --clean --fail-fast
```

The contract is static: it verifies bootstrap source, workflow ordering,
provider packaging, runtime-bundle selection, and focused frontend regressions.
It does not claim a successful Stage 2, Stage 3, or Stage 4 native build. For a
Linux LLVM bootstrap failure, inspect
`build/bootstrap/logs/x86_64-unknown-linux-gnu/stage2-native-build.log` and the
fail-only `bootstrap-failure-logs-<github.sha>` artifact before assigning the
failure to historical empty MIR.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/bootstrap/stage4_smoke_gate_spec.spl` |
| Updated | 2026-07-24 |
| Generator | `simple spipe-docgen` compatible manual |
