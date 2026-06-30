# Architecture Skill - Debugging & Feature Addition Procedures

Reference: See `ref_architecture` memory for pipeline diagrams, MIR instructions, backend details.

## Adding New Features — Checklist

1. **Lexer/Parser**: `src/compiler/10.frontend/core/lexer.spl`, `parser.spl`
2. **Source desugar**: `src/app/desugar/` (if new syntax sugar)
3. **Block parsers**: `src/compiler/15.blocks/` (if new DSL block)
4. **Type system**: `src/compiler/30.types/`
5. **HIR lowering**: `src/compiler/20.hir/`
6. **MIR lowering**: `src/compiler/50.mir/`
7. **Backend**: `src/compiler/70.backend/` (if new instruction)
8. **Standard library**: `src/lib/`
9. **Tests**: `test/`

## Debugging Pipeline Issues

```bash
# Check parse errors
bin/simple query check file.spl --format json

# Workspace diagnostics
bin/simple query workspace-diagnostics src/ --format json

# Find symbols
bin/simple query workspace-symbols --query MyType --kind class

# Trace definition
bin/simple query definition file.spl 42

# Find all references
bin/simple query references file.spl 42
```

## Lean Verification Workflow

```bash
simple gen-lean generate                    # All projects
simple gen-lean compare                     # Show status
simple gen-lean compare --diff              # Show differences
```

When modifying type inference:
1. Update `src/compiler/30.types/`
2. Update Lean theorems in `src/verification/type_inference_compile/`
3. Run `lake build` in verification project
4. Run `simple gen-lean compare`

**Generated-mirror / manual-proof split.** Keep the code-coupled `def`s (constants, geometry,
state model — the "generated mirror") separated from the hand-written theorems, so a code
change re-applies to Lean as a localized edit. Two shapes (full guide:
`doc/07_guide/compiler/lean_verification_workflow.md` § "Generated-Mirror / Manual-Proof Split"):
- **In-file marked sections** for standalone proofs checked by raw `lean <file>` (e.g.
  `examples/09_embedded/simpleos_nvme_fw/{fw,emu}/proofs/*.lean`): a `-- BEGIN gen lean … -- END
  gen lean` defs block, then a `-- MANUAL PROOFS` block. Raw `lean` can't resolve sibling
  `import`s, so both stay in one file.
- **Two files** (`Basic.lean` defs + `Theorems.lean` with `import X.Basic`) for Lake projects
  under `src/verification/<project>/`.

On a code change: re-transcribe only the `gen lean` section / `Basic.lean`, then re-check
(`lean <file>`, `lake build`, or `gen-lean compare`). Keep def names/namespaces stable.

> `gen-lean` runs a **fixed inventory** of regenerate modules — it does NOT generate Lean from
> arbitrary `@verify`/firmware `.spl`, and the CLI is currently broken (infinite recursion,
> `doc/08_tracking/bug/gen_lean_cli_infinite_recursion_2026-06-30.md`). For code outside the
> inventory, hand-transcribe the marked `gen lean` defs.

## Design Checklist

Before: Read feature spec, identify affected pipeline stages, draw dependency impact.
After: `bin/simple test`, `simple gen-lean compare` if verification affected.
