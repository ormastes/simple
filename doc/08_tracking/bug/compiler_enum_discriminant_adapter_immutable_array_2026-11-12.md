# Enum discriminant adapter: product code mutates an immutable array and a nil 'variants' access (2026-11-12)

Status: open
Area: src/compiler (enum discriminant folding adapter)

## Symptom

`test/02_integration/compiler/enum_discriminant_adapter_spec.spl` (15
examples, 6 failing under the seed on release/1.0.0). Two distinct product-side
defects:

1. "folds nested arithmetic before numbering the next implicit variant" and
   "preserves every supported operator through parsed declarations" fail with
   ```
   semantic: <spec>:154:35: cannot call mutating method 'push' on immutable
   array 'previous'
   ```
   The `previous` array lives in the adapter product code reached from the
   spec's call site; the seed rejects the mutation because the receiver is an
   immutable (`val`) array.

2. "detects a folded explicit value followed by an implicit collision" fails
   with
   ```
   semantic: undefined field 'variants': cannot access field on value of type 'nil'
   ```
   an adapter lookup returns `nil` where the spec (reasonably) expects an
   enum declaration record carrying a `variants` field.

## Root cause

The enum-discriminant adapter either declares a working array as immutable and
then pushes into it, or returns `nil` from a declaration accessor the
consumers treat as a populated record. The seed enforces array mutability
strictly, surfacing the latent bug; the `nil` access is a genuine product
robustness gap.

## Unblock

Make the adapter's accumulator array mutable (`var`) or use a builder, and
make the declaration accessor fail-closed (return the record or a named error,
never `nil`). Re-run this spec after the fix; keep the assertions as-is.
