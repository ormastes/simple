# HIR cache: building from decoded modules diverges from in-memory on the core-c-bootstrap lane

**Date:** 2026-10-19
**Lane:** Windows, `--runtime-bundle core-c-bootstrap`, LLVM backend
**Status:** open. Found while verifying the Core-C encoder node-guard fix
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
