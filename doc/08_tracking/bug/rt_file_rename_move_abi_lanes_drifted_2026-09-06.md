# `rt_file_rename` / `rt_file_move` ABI has drifted across four lanes

**Date:** 2026-09-06
**Found by:** sspec score-80 wave 16B (modernizing
`test/01_unit/compiler/bootstrap/file_rename_move_abi_contract_spec.spl`)

## Symptom

`test/01_unit/compiler/bootstrap/file_rename_move_abi_contract_spec.spl` is
RED: 3 of 3 scenarios fail. The spec pins one ABI contract for
`rt_file_rename` — a 4-argument `(ptr, len, ptr, len) -> bool` with an
EXDEV-aware rename-then-publish sequence — and four lanes each disagree with
it differently.

## The four drift points

| # | Lane | Drift |
|---|---|---|
| 1 | `llvm_lib_translate.spl` | `rt_file_rename` is not declared **at all**; only `rt_file_move` is (line 306). The LLVM codegen lane cannot emit a call to it. |
| 2 | SFFI generator specs (compiler spec line 152, app spec line 136) | Both declare `return_type: "void"` for `rt_file_rename`, contradicting the bool ABI. |
| 3 | `stubs.rs:313` / `:680` | Still lists `"rt_file_rename"` and defines a **no-op 2-argument stub**. The real backing has never superseded the stub, so calls silently do nothing. |
| 4 | `runtime.c` / `runtime_native.c` | `runtime.c` has no EXDEV/rename-publish sequence at all. `runtime_native.c` (around lines 10767-10782) implements one but names its success flag `ok` rather than `published`, breaking the asserted variable-name contract. |

## Why it matters

Drift point 3 is the dangerous one: a no-op 2-arg stub still registered under
the real symbol name means a `rt_file_rename` call compiles, links, and
returns without renaming anything. Points 1 and 2 mean the LLVM and SFFI lanes
could not agree on the signature even once point 3 is fixed.

## Unblock condition

Reconcile all four lanes on the single 4-arg `-> bool` contract the spec
pins: declare `rt_file_rename` in `llvm_lib_translate.spl`, correct both SFFI
generator specs to `return_type: "bool"`, delete the `stubs.rs` no-op and its
table row, and align the C runtime's publish-sequence naming. Then the three
scenarios in the spec go green on their existing assertions — do not weaken
them.

## Provenance note

This record was filed twice. The first copy was created by wave 16B and then
disappeared from the working tree before it was committed — untracked files in
this shared checkout are periodically swept by peer sessions. Filed again and
committed in the same change as the spec it documents.
