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
