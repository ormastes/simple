# Wine VM write-readback evidence token renamed; specs asserting the old token are RED

- Date: 2026-08-26
- Discovered during: sspec modernization batch `ora_batch_aa`
- Status: OPEN

## Symptom

`test/system/app/simpleos/feature/simpleos_wine_process_loader_runtime_spec.spl`
scenario "PEB/TEB VM byte-write readback precedes loader runtime evidence" fails
at HEAD (proven by running the HEAD blob directly: `Results: 2 total, 1 passed,
1 failed`):

```
expected ... PEBTEBLayoutVMReadback ... to contain VMWriteReadback:PEBTEBLayoutBytes
```

The implementation (`src/lib/common/wine_peb_teb*.spl` /
`wine_peb_teb_apply_layout_byte_writes`) now emits the evidence token
`PEBTEBLayoutVMReadback`; the spec asserts the older token
`VMWriteReadback:PEBTEBLayoutBytes`.

## Scope

`grep -rln 'VMWriteReadback:PEBTEBLayoutBytes' test/` shows ~10 specs still
asserting the old token, including
`test/01_unit/lib/common/wine_process_session_loader_runtime_spec.spl`,
`wine_dll_view_tls_dispatch_vm_write_spec.spl`, and siblings.

Confirmed RED at pre-edit baseline during the same batch (same assertion,
same stale token):
- `test/system/app/simpleos/feature/simpleos_wine_process_vma_relocation_spec.spl`
  (modernized 49 -> 100; scenario 1 green, scenario 2 red on this token)

## Decision

Per testing rules the spec is left RED (assertion not weakened); it documents
stale evidence-token naming after an implementation rename. Unblock condition:
decide the canonical token name; either the implementation restores the old
token or all affected specs are updated in one reviewed change.

## Note

The loader-runtime spec itself was modernized in the same session (score
49 -> 100, `effective_aggregate=100`); the failing assertion is byte-identical
to HEAD's.
