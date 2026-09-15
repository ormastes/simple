# file_read definitions drifted to optional returns

Date: 2026-09-15
Discovered by: test-wave agent B (spec triage)

## Affected spec (left RED)
- test/01_unit/lib/nogc_sync_mut/file_read_single_return_type_spec.spl
  (3 of 9 its fail)

## Observed
Two definitions of file_read in src now return an optional; the spec pins a
single plain `text` return type across all definitions.

## Unblock condition
Decide the contract: restore the total text return, or re-pin the spec to
the optional-return design deliberately.
