# Duplicate `backend_types` terminal declarations

Status: OPEN (P2)
Status re-verified 2026-08-17 by source inspection (triage shard 01).
terminal declaration, in `compiler.backend.backend.backend_types`. The wider
family of multiply-declared enums with divergent variant orders is STILL OPEN,
and nothing in the repo detects it (see the sabotage section).

## What was fixed

`src/compiler/70.backend/backend_types.spl` (call it A) ends with

    export use compiler.backend.backend.backend_types.*

so it already re-exported every name from
`src/compiler/70.backend/backend/backend_types.spl` (B) — and it ALSO declared
its own `BackendKind`, `CompiledSymbol` and `CompiledSymbolKind`. A single
`use compiler.backend.backend_types.*` therefore delivered each of those three
names from two terminal modules at once, which blocked Stage 3 self-host:

    error: in-process native-build: HIR lowering error in
    src/compiler/backend/backend/interpreter.spl: enum payload dependency
    `CompiledSymbolKind` conflicts:
      `compiler.backend.backend_types::CompiledSymbolKind::enum` vs
      `compiler.backend.backend.backend_types::CompiledSymbolKind::enum`

The `src/compiler/backend -> 70.backend` symlink is NOT involved. Both module
paths are derived from real, distinct files: A from `70.backend/backend_types
.spl` and B from `70.backend/backend/backend_types.spl`. Stripping the numeric
directory prefix yields `compiler.backend.backend_types` and
`compiler.backend.backend.backend_types` respectively, with or without the
symlink.

A no longer declares the three names; it imports them from B and lets the
pre-existing wildcard re-export carry them to every importer. One terminal
declaration per name.

## The third copy — FIXED 2026-08-04 (`c764ffdbd854`)

`src/compiler/10.frontend/core/backend_types.spl` (C) declared a THIRD
`BackendKind`. All three carried the same 21 variant NAMES in three different
ORDERS, so the divergence was purely positional and therefore silent:

| copy | file | `Byl` index | status |
|------|------|-------------|--------|
| A | `70.backend/backend_types.spl` | 13 | declaration removed by `0ae169b85918`; re-exports B |
| B | `70.backend/backend/backend_types.spl` | 6 | **the single terminal declaration** |
| C | `10.frontend/core/backend_types.spl` | 9 | declaration removed by `c764ffdbd854`; re-exports B |

Same-named enums collapse in the global enum registry — whichever declaration
registers first fixes the discriminants for every importer — so a value encoded
against one order and decoded against another is a DIFFERENT variant. A wrong
answer, not a crash.

C also carried a fourth hand-written copy of the same ordering as integer
constants (`BACKEND_CRANELIFT = 0` … `BACKEND_AUTO_JIT = 20`, `BACKEND_BYL = 9`).
That mirror is load-bearing, not decorative: `impl BackendKind.supports_target`
compares an enum value against those integers, so drift there silently reroutes
every backend capability query. It is renumbered to B's order. `backend_kind_name`
was additionally missing its `BACKEND_BYL` arm outright and answered `"unknown"`
for byl; added.

No file was deleted. C still solely provides `CodegenTarget`, `OptLevel`,
`OutputFormat`, the `TARGET_*` / `OPT_*` / `OUTPUT_*` integer tags and their
name/predicate helpers — deleting it would have rerouted callers, not deduped.

### Reachability of C — measured, not assumed

A third declaration that is genuinely isolated is a lower severity than one
sharing a registry. C is **not** isolated:

- **C is a live, loadable module under TWO module paths.** Positive-capability
  probe on `opt_level_name`, a symbol declared nowhere else in the tree
  (`/usr/bin/grep -rn '^fn opt_level_name' src/` → one hit, in C):
  both `use compiler.core.backend_types.{opt_level_name}` and
  `use compiler.frontend.core.backend_types.{opt_level_name}` resolve and return
  `"none"` for `opt_level_name(0)`. The numeric layer prefix `10.frontend` is
  reachable both stripped-to-`frontend` and dropped entirely.
- **`compiler.core`'s package manifest re-exports C's copy by name.**
  `src/compiler/10.frontend/core/__init__.spl` declares `mod backend_types` and
  then `export BackendKind, … CompiledSymbol, CompiledSymbolKind`, so every
  `use compiler.core.*` importer received C's variant order rather than B's.
  Four in-tree files do exactly that: `src/lib/nogc_sync_mut/failsafe/mod.spl`,
  `src/lib/nogc_async_mut/failsafe/mod.spl`,
  `src/lib/nogc_async_mut/debug/coordinator.spl`,
  `src/lib/nogc_async_mut/mcp/session.spl`. One test spec imports C directly:
  `test/03_system/feature/usage/.spipe_matchers_wasm_compile_spec.spl`.
- **C is NOT in the transitive `use` closure of the bootstrap entry.** Static
  closure from `src/app/cli/bootstrap_main.spl` reaches 340 modules; B is in it,
  C is not. So C never shared a lowering scope with B and never reproduced the
  payload-conflict error that exposed A. That is why this was latent rather than
  a hard Stage 3 block — one `use compiler.core.*` from a compiler module away
  from live.

### Also found while measuring

- `compiler.core.__init__` exports `OptimizationLevel` from `backend_types`, but
  C declares `OptLevel`, not `OptimizationLevel` — a dangling export. The spec
  above asks `compiler.core.backend_types` for `OptimizationLevel`, which only B
  has ever declared. Not fixed here.

## Sabotage check — NOTHING observes a divergent duplicate (open gap)

Reintroducing a second divergent `BackendKind` in C (`Byl` moved from index 6 to
index 0) and loading it into the SAME compilation as the terminal produced no
diagnostic, no warning and no behaviour change: a probe importing C
(`opt_level_name`) and B (`BackendKind`, `compileerror_backend_error`) printed
the identical `Compile error in backend (byl): m` before and after, exit 0.
Seed evidence (`bin/release/x86_64-unknown-linux-gnu/simple`, which self-labels
as a bootstrap seed).

So there is no check, lint rule, spec or build diagnostic in the repo that
detects a second divergent terminal declaration of the same enum name. The only
thing that ever caught this family was the HIR payload-dependency conflict in
`0ae169b85918`, and that fires only when both terminals are visible through ONE
`use` wildcard — not when they are merely co-loaded. Both prior fixes were found
by hand.

**This gap is the reason the family below is still open.** A duplicate-terminal
check belongs in `scripts/check/` or as a lint rule.

## The rest of the family (enumerated, still open)

`find . -name backend_types.spl` outside `.claude/worktrees/` returns exactly
the three files above. But `BackendKind` was not the only name they multiply
declare, and this shape is repo-wide. A scan of every `enum` declared in more
than one file under `src/` (excluding `src/compiler_rust/` and vendored trees),
keeping only those whose declarations disagree on variant ORDER while sharing at
least two variant names, returns **29 enums**. Highest risk first — the two
whose copies live in the SAME package are near-certain to be co-loaded:

| enum | decls | orders | files |
|------|-------|--------|-------|
| `ConcreteType` | 2 | 2 | `40.mono/monomorphize/{types,engine}.spl` — same package |
| `Severity` | 2 | 2 | `00.common/error.spl`, `00.common/diagnostics/severity.spl` — same package |
| `CompletionKind` | 2 | 2 | `90.tools/query_types.spl`, `15.blocks/blocks/definition.spl` |
| `BinOp` | 3 | 2 | `10.frontend/parser_types_expr.spl`, `lib/common/parser/ast.spl`, `lib/gc_async_mut/pure/ast.spl` |
| `ValueKind` | 7 | 3 | `app/interpreter/core/value.spl` + 6 under `src/lib/` |
| `Architecture` | 6 | 3 | `app/debug/remote/types.spl`, `app/mcp/dap_types.spl`, +4 |
| `ImportKind` | 5 | 3 | `00.common/dependency/graph.spl`, `90.tools/depgraph/parser.spl`, +3 |
| `VariableScope` | 7 | 2 | `90.tools/sffi_gen/specs/interpreter_hooks.spl`, `runtime/hooks.spl`, +5 |
| `HttpStatus` | 4 | 2 | `app/io/http_{ffi,sffi}.spl`, +2 under `src/lib/` |
| `Js{Statement,Expression,Value}` | 3 each | 2 each | `lib/{nogc_sync_mut,common,}/js/types/` |
| `Stmt`, `Pattern`, `Literal` | 2–3 | 2 | `lib/common/parser/ast.spl`, `lib/gc_async_mut/pure/ast.spl`, `app/interpreter/ast_types.spl` |
| `Value` | 3 | 3 | `70.backend/backend_types.spl`, `lib/nogc_sync_mut/src/di.spl`, `lib/gc_async_mut/pure/evaluator.spl` |
| `VulkanCommand3DKind` | 2 | 2 | `lib/{nogc_sync_mut,nogc_async_mut}/engine/render/vulkan_commands.spl` |

Plus the names the three `backend_types.spl` files still multiply declare, which
this fix deliberately did not touch:

- `CompiledSymbolKind` — 3 declarations (A, B, C), but `Function, Data, Const`
  in all three, so structurally safe TODAY. Order-safe by luck, not by
  construction.
- `struct CompiledSymbol` — 3 declarations with divergent FIELD order
  (B: name/kind/address/size; C: name/kind/address/size; A: name/address/size/kind).
- `CodegenTarget` — 2 (B, C). `BuildMode` — 3 (B, C, `80.driver/build_mode.spl`).
- `OutputFormat` — 5 declarations, three of them inside the compiler
  (`70.backend/linker/link.spl`, `00.common/driver_core_modes.spl`, C).

## Working-copy hazard observed 2026-08-04

The shared working copy held a copy of A that still declared `BackendKind`,
i.e. a REVERT of `0ae169b85918`, while origin's A was correct. Committing the
working copy wholesale would have reintroduced copy #1. Verify A against origin
before landing anything that touches `70.backend/backend_types.spl`.

## Reproduction

Replay the recorded Stage 3 command against the Stage 2 self-hosted binary
(bare positional `.spl` form, no `--entry` / `--source`, cranelift backend):

    build/bootstrap/stage3/<triple>/stage2-admitted/simple native-build \
      --target <triple> --backend cranelift --runtime-bundle core-c-bootstrap \
      --mode dynload -o <out> src/app/cli/bootstrap_main.spl
