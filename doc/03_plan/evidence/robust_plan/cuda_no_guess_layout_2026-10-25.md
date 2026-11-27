# CUDA no-guess layout repair

Selected scope: remove unresolved aggregate-field, field-access and GEP layout
fallbacks. The MIR module type table remains the canonical layout authority.
No portable schema, runtime/provider selection or aggregate ABI changes.

The four lowering owners return `Result<(), CompileError>` and instruction
lowering propagates errors. Module compilation therefore returns an error
instead of a PTX module when layout admission fails. Construction uses the
destination field layout and validates kind, arity and scalar field types.
Get/set validate scalar transfer types. Compound field transfers and
multi-index GEP fail explicitly. Array field access checks its index bounds.
Tuple stride now includes member and trailing alignment, matching field offsets.

Layout admission follows struct fields and enum payloads, validates nominal
entry kinds and rejects unresolved or cyclic by-value graphs with a depth limit
of 32. Pointer indirection terminates traversal. The depth limit is a bounded
recursion guard, not a measured total traversal/RSS guarantee; repeated DAG
subgraphs are not memoized. Existing MIR offsets and integer representability
remain producer contracts; this repair does not certify arbitrary corrupted
layout records or introduce a new portable layout validator.

Production compilation still rejects aggregate-valued locals. The construction
owner's failure cases are direct unit evidence only. Known-layout production
positives use pointer GetField/SetField/GEP. No new storage or return ABI is
claimed. Internal numeric size/alignment helpers require prior successful
admission against the immutable module type table.

Changed regression specifications:

- `test/01_unit/compiler/codegen/cuda_backend_intensive_contract_spec.spl`:
  missing layout failures, nested missing/wrong-kind/cycle failures, scalar
  transfer contracts, aggregate kind/count/type refusal, array bounds, mixed
  struct field offsets and padded struct/tuple strides. Restores missing
  primitive and typed-module fixture helpers already referenced by the suite.
- `test/01_unit/compiler/backend/cuda_source_global_pointer_abi_spec.spl`:
  source-to-PTX u16 buffer load/store widths.

## Evidence status

STATUS: WARN — execution pending, not release-qualified.

The initial negative specification was authored before replacing the fallback.
A red execution was not run: the shared Phase 3 matrix occupied roughly
44 GiB of its 48 GiB resource cap and the coordinator prohibited test/build
launches. No executed TDD cycle or passing runtime regression is claimed.

`direct-env-runtime-guard.shs --working` and `--staged` passed.
`find doc/06_spec -name '*_spec.spl' | wc -l` returned 0.
Source architecture review accepted the scoped admission strategy, subject to
final source and runtime review. No heavy build or Rust-seed fallback was used.

Ownership: CUDA lane; final reviewer and merge owner: root agent.
Sidecars: N/A. Architecture review: existing robust remaining-lane reviewer.
