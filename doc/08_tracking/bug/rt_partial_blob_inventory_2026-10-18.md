# Mixed HIR encode refusal drops RT validation coverage

Bug ID: `rt_partial_blob_inventory_2026-10-18`.
Severity: P1, confirmed source-level validation bypass.
Bug DB reconciliation pending: qualified normal DB tooling is unavailable.
Fix base: `2bcc8144b1bf4b16af66d6c0a5c9bd76e1c3ac8f`.
Native regression and compiler/core/full-CLI verification are UNRUN.

PR #3657 (`b3b352f2fab3c28371c2a576f40059fa232616d1`) retains every module
in validation_module_array but omits the blob and parallel hints when encoding
returns empty. The blob validator uses the fallback array only when *all*
blobs are absent. For a valid ordinary module A and refused module B containing
an @rt(hal) function, the nonempty [A] blob route validates only A. With no flat
registry claims, it finds no HAL root and returns success without admitting B.

Relevant reviewed source locations:
- driver_hir_pipeline_lowering.spl:2067 and 2080: full array versus filtered blobs.
- driver_hir_pipeline_support.spl:273: passes both inventories to RT validation.
- rt_criticality_validation.spl:737 and 760: all-empty fallback versus decoded-only admission.

The fix verifies supplied blobs with the existing decode/canonical checks,
then requires their count to match a nonempty fallback inventory before RT
policy runs. A mismatch clears capabilities through the same owner operation
as codec failures and returns fatal RT-E-HIR-BLOB-INVENTORY. Malformed and
noncanonical blobs retain their original diagnostic precedence. Blob-only
callers and the established all-empty genuine-module fallback remain supported;
the fix does not introduce a new Dict-read fallback.

Count equality is sufficient for the current producer contract: every source
iteration appends one module and at most one corresponding successful blob.
Every omitted blob strictly lowers the count. This is not a general module
identity/set proof against callers that substitute or duplicate arbitrary blobs.

The real HIR regression includes an inadmissible HAL root without flat registry
claims and confirms the intact fallback diagnoses its unbounded allocation.
It then supplies only the ordinary module blob with the full fallback array,
in both omission positions, and requires fatal incomplete-inventory diagnostics
and capability invalidation. A separate malformed partial-input regression
preserves RT-E-HIR-BLOB-DECODE. No codec corruption or native run is simulated
as successful evidence; the omitted blob models the producer refusal handoff.
