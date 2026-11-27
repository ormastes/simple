# Extern `*mut T` out-params have no non-retaining contract (2026-10-24)

Class: source classification record for the Phase-3 run-11 borrow failures
in `compiler.backend.linker.lld_sffi` (`6:1`) and
`lib.nogc_sync_mut.sffi.dynamic` (`4:1`, `6:1`). No source change.

## Sites

- `src/compiler/70.backend/linker/lld_sffi.spl:48` `lld_elf_link`:
  `spl_dlsym_process_checked("simple_lld_elf_link", &mut fptr)`.
- `src/lib/nogc_sync_mut/sffi/dynamic.spl:95,108,139,166`:
  `spl_wffi_try_call_i64_out(..., &mut probe|value)`,
  `spl_dlopen_checked(path, &mut handle)`,
  `spl_dlsym_checked(handle, name, &mut symbol)`.

Each passes a fresh `&mut local` to an `@unsafe(..., capabilities: [ffi,
raw_ptr])` extern whose last parameter is a `*mut i64` status/out slot,
inside an explicit `unsafe(capabilities: [ffi, raw_ptr])` block. The runtime
writes the slot during the call and does not retain it.

## Classification

These modules are legacy (no `@no_gc(strict)`). In legacy modules the
diagnostic is the checker false positive recorded in
`legacy_direct_call_short_contract_unsatisfiable_2026-10-24.md` (fixed in the
checker; every direct `f(&mut x)` was rejected, not only externs). The source
is correct and stays as is.

## Gap (strict mode, open)

`declared_param_effect` / `_param_effect`
(`src/compiler/35.semantics/param_effects/{contracts,infer}.spl`) mark every
extern pointer/reference parameter `foreign-unknown`, and
`publish_short_call_contracts` drops extern rows. There is no annotation that
declares an extern out-slot non-retaining (grep for
`non_retaining|noescape|@out` finds none). If these modules become
`@no_gc(strict)`, the same calls are true positives under the current policy,
and the only alternatives are a heap cell plus raw read-back (changes the
`*mut i64` signature contract) or a new checked extern-contract attribute. The
attribute is the right fix and needs a design. Do not paper over it with an
unchecked blessing.
