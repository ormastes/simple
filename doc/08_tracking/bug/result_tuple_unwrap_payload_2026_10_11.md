# Result tuple unwrap loses the aggregate payload contract

Status: OPEN — source repair and regressions authored; native and compiled unit execution pending.

## Actual failure

Producer `892b220e19b5cbafd620190c95b9a2f26fc5ebc08304b8b07d4475da0ea7abb0`,
source `b58baa89e4d65a40768fceaf8221fdbdbe58da24`, reaches PostgreSQL MIR and
rejects `src/lib/common/search/ranking.spl:268:5`: `result.unwrap().1`.
`_idf_fixed_checked` returns `Result<(i64, i64), text>` with
`Ok((argument, idf))`; `idf_fixed` returns 0 on Err and reads the second tuple
field on Ok. This is unrelated to the three capped underconstrained Err witness
calls in the Phase3 lane.

Retained evidence under `/mnt/c/Temp/simple-phase2-cuda-owner-20261011`:

- `b58-phase4-essential-collection-v1/postgres/build/build-evidence.json`:
  SHA256 `53ead0ea0a2827acfc6aac636bda3ffceac1a85f3c384567a740668d367b51cc`.
- Its `build.log`: SHA256
  `045ecae48ae8f1f1db2e5e9f6205c69c8c79aec950f5018e5153d53e4a2e90a4`.
- `postgres-result-tuple-unwrap-source-diagnosis.json`: SHA256
  `d37792c426a851f4c50d0668504edc0cbcc8f652d66c2e71e4f140acf5700aac`.

The diagnostic occurs three times by log replay, representing one unique site.
Release `226d6963aa9e59a97d0db219553a15394c38650f` has the identical ranking
caller and identical unwrap payload acceptance switch: no Tuple arm. Its
prelowered-receiver helper does not repair this unsupported payload.

## Representation and repair boundary

Ordinary tuples are `AggregateKind.Tuple` with exact element MIR types. Both
LLVM (`aggregate_intrinsics.spl:180`) and Cranelift
(`cranelift_codegen_adapter.spl:722`) allocate raw heap storage, one word per
field. `Ok(tuple)` passes that pointer as the `rt_enum_new` payload word;
the runtime stores it unchanged. It is **not** the header-bearing `rt_tuple_new`
container used to pack several arguments of an enum variant.

Recover a supported tuple with a pointer-sized `Cast` to `Ptr(tuple_type)` and
a `Copy` into a fresh local of that exact tuple type. Both backends preserve the
pointer while tuple projection can recover field types and offsets. Do not cast
directly from i64 to Tuple: Cranelift's generic numeric cast compares aggregate
byte size, so a small boolean tuple would take an invalid width-conversion path.
Do not retag the original scalar local or call `rt_tuple_get` on raw storage.

The source repair admits nonempty tuples whose leaves are i64, bool or f64,
including nested tuples, for `unwrap()` and `unwrap_err()`. The Result-only `?`
payload branch restores the same type on success. The generic custom-enum and
Option payload decoder remains unchanged. The existing Err branch
still drops owned resources, aborts an active MC/DC decision, and returns the
same Err wrapper. Receivers are evaluated once. Scalar/array/struct unwrap
behavior is unchanged. Tuple `unwrap_or`, empty/unit payloads, text, nominal
records/classes, collection fields, unresolved and other primitive widths are
not newly admitted. Unsupported tuple fields remain fatal; additional owner
provenance and text representation work is a separate feature.

An initial incomplete Cranelift source excerpt suggested a stack-lifetime
blocker. Reading its explicit Tuple arm disproved that hypothesis: it already
uses `rt_alloc`, and Tuple is a runtime-handle local. The external source plan
preserves this correction and the exact relevant source pins.

## Regression and qualification requirements

- `test/01_unit/compiler/mir/result_tuple_unwrap_spec.spl`: ten compiled-only
  cases exercise actual frontend/MIR pair projection, receiver evaluation once,
  nested mixed types, a two-bool pointer bridge, `?` to a new Ok constructor,
  real lower_try cleanup/return identity, unsupported fields, unsupported `?`
  fields, and an unchanged scalar control.
- `test/fixtures/compiler/result_tuple_unwrap/main.spl`: direct unwrap and
  roundtrip `?` values, Err propagation and skipped success side effects,
  exact call counts, nested numeric/bool values, tiny tuple, tuple error and
  scalar controls. Expected natural exit 0.
- `test/fixtures/compiler/result_tuple_unwrap/wrong_variant.spl`: must execute
  the genuine wrong-variant panic, never succeed or return a fabricated tuple.

All are AUTHORED_UNEXECUTED. First qualify the new producer with its own Hello,
then build/link/run the positive and panic fixtures through actual LLVM and
Cranelift owners with pinned runtime/source identities. Require the ten unit
cases to actually execute under a qualified full CLI, with no skips/failures.
Finally compile the unchanged ranking provider and the PostgreSQL closure;
other PostgreSQL failures remain independent. No seed test fallback, forced
cache admission, existing caller rewrite, or claim of full PostgreSQL repair.

## Release forward port (source-only)

This port targets release `8303221132a0e44a739b30f92c3a1b7723534e86`
from the independently reviewed b58 repair
`6528e86990ea1cc069b4a06b9e049482bbb625fc`. Tuple admission and recovery
now reside in the release's `lower_result_unwrap_core`; its prelowered receiver
parameter and single-evaluation selection are preserved. The tenth MIR case
asserts both actual runtime-call operands use that prelowered local rather
than a different bound receiver local. The other nine cases and both native
entries retain their original assertions. All ten cases remain unexecuted.

The release's scalar Optional boxing, narrowing, conditional-arm handling,
comparison and extern ordering fixes are untouched. The complete prior
`lower_try_expr` method matched b58 before this narrow Result-only addition.
The LLVM tuple emitter, Cranelift adapter and MIR type representation match
the reviewed b58 blobs; the enum runtime payload-storage section is unchanged.
No release producer qualification or PostgreSQL completion is inferred.
