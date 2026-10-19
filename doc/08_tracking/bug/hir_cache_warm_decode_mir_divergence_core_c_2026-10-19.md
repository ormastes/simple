# HIR cache: building from decoded modules diverges from in-memory on the core-c-bootstrap lane

**Date:** 2026-10-19
**Lane:** Windows, `--runtime-bundle core-c-bootstrap`, LLVM backend
**Status:** fixed on `work/hir-codec-warm-decode-20261019` (see "Root cause" at
the end). Found while verifying the Core-C encoder node-guard fix
(`rt_heap_ref_registered` standalone; branch `work/hir-cache-core-c-node-guard-20261019`).

## Context
Before that fix, no HIR module was ever stored on this lane: `stores=0` and
every module was refused with `unregistered HirModule node`. So no build on
this lane had ever compiled from decoded HIR. Now that stores work, warm
builds load decoded modules. One closure shows that the decoded HIR is not
equivalent to the HIR lowered in memory.

## Evidence
The test producer was built by the tracked Rust seed from `origin/release_phase3`
`5b17c46af1f` plus the node-guard fix. It was then relinked with
`runtime_core_intrinsics.obj` (the producer4 recipe).

| probe closure | run | HIR cache | MIR error lines | result |
|---|---|---|---|---|
| std only (sha256, utf8; 12 modules) | no cache / cold / warm | stores=12, then hits=12 | 0 / 0 / 0 | identical program output |
| entry importing `compiler.hir.hir_codec` (321 modules) | `SIMPLE_HIR_CACHE=0` | -- | 1281 | rc=1 |
| same | warm (hits=321) | hits=321 | 1336 | rc=1 |

The in-memory run already fails on this lane. Only the decoded runs add
**75** `MIR lowering received a garbage expression handle (mis-extracted enum
payload)` errors. Those come from `expr_dispatch.spl:6387`: an `HirExprKind`
that is not a live boxed enum (`_sffi_enum_discriminant < 0`). The decoded runs
also have 19 fewer `enum construction ... payload type mismatch` errors. Every
one of the 321 modules passes `SIMPLE_HIR_CODEC_ROUNDTRIP=1`
(`ok=true stable=true`). That means `encode(decode(m)) == encode(m)` holds,
but decode does not rebuild a value MIR can consume for some expression kind.

## Next step
Attribute the module. `error_fatal(..., nil)` carries no span, so add the
module and function name to that diagnostic, or bisect by deleting cache
entries. Then fix the decoder arm. Until then, compare cold and warm outputs
before trusting a warm build that loads compiler modules from the cache on
this lane.

## Root cause (2026-10-20)
The generated decoder wrote every optional field as `field = Some(ov)`, where
`ov` was already a `T?` local holding the bare decoded node. Fresh HIR
lowering stores the bare node instead (`expression_core.spl`, Range:
"bare-lift"). `if val` unwraps both shapes the same way, so the encoder
round-trips them. But a consumer that passes the optional field straight
through gets the Option box. The MIR case is `struct_construct_spread_base`:
it returns `Range.end` of a paren-form `Ctor(..base, ...)` spread into
`lower_expr`. That reads the box as a `HirExpr`, which gives the 75
`garbage expression handle` errors (`SIMPLE_MIR_GARBAGE_EXPR_DEBUG=1` puts
the parent at `tco.spl:116`, `MirFunction(..func, blocks: new_blocks)`,
bits `0x4`).

A seed-built native probe against the real codec confirmed it. It decodes
`Range(nil, <expr at line 41>)` and passes `end` through unwrapped. With the
old codec it reads line `3`; with the regenerated codec it reads `41`.

A "cold" run with the cache on already decodes: the HIR shard workers store,
and the main process loads from the cache. That is why such a run also shows
the 75 errors. Only `SIMPLE_HIR_CACHE=0` is truly in-memory.

Fix: `codec_gen.spl` assigns the bare `ov` for node/opaque inner types. Scalar
and list optionals keep `Some(...)`, since a probe shows the same behaviour
for both shapes. `hir_codec.spl` was regenerated: 24 lines, no other drift.
Spec: `test/01_unit/compiler/hir/hir_codec_optional_node_bare_spec.spl`.
