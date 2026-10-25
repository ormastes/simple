# Result<Struct> payload pushed into [Struct] crashes (2026-10-25)

Status: OPEN. bug_db.sdn: DB reconciliation pending. Source workaround on work/p3fix-g2cold (2 sites); compiler root fix
candidate is PR #4667's box_runtime_value record guard (unproven for this shape,
it lands only through the Phase 3 self-rebuild).

## Symptom
Phase 3 gen-1 (`S/r27/bp/simple.sw28a`, sha 4361d928) on the WORKER path
(`native-build --entry ...`): every module compiles, then the worker SEGVs in
`compiler.driver.cache.cold_hir_native_object_persistence_v1.cold_hir_native_objects_persist_v1+0x5a8`
<- `driver_cold_hir_persist_verified_objects_v1` <- `compile_to_native`, before
the link. `for receipt in receipts` reads element 0 as `0x5b9bbbf237c88` = a heap
handle shifted left by 3 (rt_value_int_wide of a struct pointer), then loads
`receipt.seed`. Same site as pu9 (bypass agent, update 9).

## Producer
Both producers of `ctx.cold_hir_typed_receipts` have this shape:

```
match f(...):
    case Err(reason): ...
    case Ok(receipt): receipts.push(receipt)
```

Disassembly of sw28a: `driver_hir_archive_cold_capture_v1+0x47a4` and
`cold_hir_typed_receipts_from_lowered_sources_v1+0xec4` each call
`rt_value_int_wide` immediately before `rt_array_push`.

## Minimal repro (Stage 2, `S/r27/stage2-simple`)
`src/app/zz_g2cold/{a..j}.spl` in worktree simple-p3fix-g2cold (positional native-build):

| variant | form | Stage 2 result |
|---|---|---|
| a | `case Ok(receipt): xs.push(receipt)` | SEGV before first print |
| b | `val typed: Rc = receipt; xs.push(typed)` | SEGV |
| c, h | `val r: Rc = res.unwrap(); xs.push(r)` | SEGV |
| f | a, Ok-only (no Err taken) | SEGV |
| d | `xs.push(Rc(...))` direct ctor, no Result | PASS |
| i | `xs.push(Rc(name: receipt.name, n: receipt.n))` | PASS |
| j | nested-struct Outer rebuilt from fields | PASS |

So a Result payload (matched or unwrapped, typed or not) loses its struct
provenance and is int-boxed by the push; a freshly constructed struct is not.

## Workaround
Rebuild `ColdHirTypedReceiptV1(seed:, abi_payload:, interface_content:)` from
the payload's fields before the push (variant j shape), tagged
`@workaround bug=result_struct_payload_pushed_into_struct_array_crashes_2026-10-25`:
- `src/compiler/80.driver/cache/driver_hir_archive_cold_boundary_v1.spl`
- `src/compiler/80.driver/cache/cold_hir_semantic_seed_v1.spl`

Retire when a generation built by a compiler carrying the root fix runs
variant a correctly (spec below).

## Spec
`test/01_unit/compiler/codegen/native_result_struct_payload_push_spec.spl`.
