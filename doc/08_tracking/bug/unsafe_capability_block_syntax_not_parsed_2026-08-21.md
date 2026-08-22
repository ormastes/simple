# `unsafe(reason: ..., capabilities: [...]):` block syntax does not parse as an unsafe block

Date: 2026-08-21
Reporter: agent A5+Y2 (Any hardening)
Status: OPEN — recorded, not worked around silently.

## What the plan asks for

`doc/01_research/compiler/hardening/simple_hardening_plan_2026-08-21.md` §8.1 makes
this the PRIMARY spelling of a capability-scoped unsafe region:

```simple
unsafe(
    reason: "decode legacy plugin payload",
    capabilities: [type_erasure]
):
    val raw: Any = legacy_plugin.read()
```

## What actually happens

Measured against the deployed `bin/simple` on 2026-08-21 by lowering a fixture to
HIR and inspecting the resulting `HirExprKind`:

```simple
fn g() -> i64:
    unsafe(reason: "decode", capabilities: [type_erasure]):
        val y: Any = 2
    4
```

The body does NOT become `HirExprKind.UnsafeBlock`. The statement lowers to an
ordinary expression statement (the probe reported `expr other`), so the block is
not an unsafe region at all: `safety_checker.spl`'s `in_unsafe` never turns on for
it, and `35.semantics/any_escape` cannot see a region there either.

The bare form parses correctly:

```simple
unsafe:
    val y: Any = 2          # -> HirExprKind.UnsafeBlock, confirmed
```

and the §8.1 fallback annotation form parses too:

```simple
@unsafe(reason: "decode", capabilities: [type_erasure])
fn h() -> i64:
    unsafe:                 # -> HirExprKind.UnsafeBlock, confirmed
        val z: Any = 3
```

## Consequence and current workaround

`any_escape` uses the §8.1 ANNOTATION form (`@unsafe(...)` on the declaration plus
a bare `unsafe:` block inside), exactly as §8.1 permits, and the fixtures under
`test/fixtures/any_escape/` are written that way. This is a deliberate use of the
documented alternative spelling, not a silent normalization: the block form is
recorded here as unimplemented.

## Fix location

`src/compiler/10.frontend/core/_ParserDecls/enum_module_body.spl` already parses
`@unsafe(reason:, capabilities: [...])` for DECLARATIONS (lines 941-963). The
statement-position `unsafe` parser needs the same argument-list branch, and the
parsed capability list needs to reach `HirExprKind.UnsafeBlock` — see the sibling
record `unsafe_capabilities_not_carried_into_hir_2026-08-21.md`, which is the
other half of the same gap.

## Resolution (2026-08-21)

Status: RESOLVED (pending spec run — see evidence below).

- `src/compiler/10.frontend/core/parser_stmts.spl`: the statement-position
  `unsafe` / `danger` branch now also accepts `unsafe(reason: "...",
  capabilities: [a, b]):` — same argument grammar as the declaration-level
  `@unsafe(...)`. Anything else after `unsafe(` rolls back to the previous
  behaviour (an ordinary expression statement), so `unsafe(x)` calls are unchanged.
- `src/compiler/10.frontend/core/_AstExpr/nodes.spl`: `expr_unsafe_block_with_caps`
  stores the names on the flat node's S slot; `_FlatAstBridge/convert_nodes.spl`
  splits them back out; `ExprKind.UnsafeBlock` is now `UnsafeBlock(Block, [text])`
  (`parser_types_expr.spl`).
- Unknown capability names are a lowering diagnostic (see the sibling record).

Evidence: `test/01_unit/compiler/semantics/any_escape/unsafe_block_capabilities_spec.spl`
— scenario "parses the block form into HirExprKind.UnsafeBlock carrying its
capabilities" (fixture `test/fixtures/any_escape/block_form_type_erasure.spl`),
which pre-fix returned `["<none>"]` because the statement was not an UnsafeBlock.

## Hosted function-body regression (2026-08-22)

A strict source-matched stage-3 build exposed a second entry path for the same
syntax. `parser_decls_fn.spl` imported `parse_block` through the legacy
`compiler.core.parser_stmts` alias. In a restricted entry closure that owner did
not resolve to the capability-aware statement parser, so every scoped FFI block
inside `HostedCocoaBackend` and four such bodies inside `HostedSdl2Backend`
lowered `ffi` as an ordinary identifier. Cranelift then failed closed with
`GlobalLoad: unresolved identifier 'ffi'`.

The function-declaration owner now imports the canonical
`compiler.frontend.core.parser_stmts.{parse_block}` surface. The bounded
`scripts/check/check-unsafe-capability-metadata-ownership.shs` preflight scans
the frontend owner directory for any reintroduced legacy import and pins both
production hosted backends as regressors. The gate reads seven fixed source
files plus the small frontend-owner directory, performs no compiler launch,
build-cache walk, or heap-sensitive runtime work, and is intended to stay well
below the 15-second bootstrap preflight budget.
