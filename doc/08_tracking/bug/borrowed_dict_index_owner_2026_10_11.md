# Borrowed dictionary indexing loses its collection owner

Status: OPEN. Candidate compiler repair; native and MIR regressions authored but UNRUN.
GitHub: https://github.com/ormastes/simple/issues/3078 (bug).
Canonical ID: `borrowed_dict_index_owner_2026_10_11`.

The admitted Phase 2 test-runner build from frozen source
`a51194b96b5f5ce3fa57670bc62a15c2414388bf`, producer SHA256
`e6447d0d10f2c8ae552b67da8420a7e581a22bb55f79e4d4e4d30b981f095811`,
fails LLVM verification while compiling `test_runner_mcdc_formal_context`.
`runner_mcdc_eval_program_cached(program: text, row: McdcEvaluation,
cache: mut Dict<text, i64>)` calls `contains_key` successfully but emits
`%l28 = getelementptr ptr, ptr %l3, i64 %l1` for `cache[program]`, even though
`%l1` is the text pointer parameter. Its write also incorrectly calls
`rt_array_set`; inserting a ptr-to-int conversion would hide one diagnostic
and retain wrong semantics.

## Root cause and correction

HIR and MIR preserve the mutable parameter as `Ref(Dict(K,V), true)`.
Dictionary methods already recognize this view and pass its runtime handle
unchanged. `local_is_runtime_dict`, the shared index read/write predicate,
recognizes only bare MIR `Dict`. The dictionary getter and compound-read
value-type resolver also recognize only bare dictionary types. Merely marking
the local as a dictionary would still decode non-integer values as i64.

The candidate introduces exact Dict/Ref(Dict) value-type recovery for MIR
and HIR. Index dispatch, getter decode and compound-read decode share it.
Reference/ownership metadata and the handle ABI remain unchanged. The view
does not claim arbitrary pointers, array references or nested references.
No application workaround, LLVM coercion, seed edit or stub is introduced.

## Evidence

- Failure ledger and preserved log directory:
  `/home/yoon/dev/simple-bootstrap-c06-20261011/build/native_probe/phase3-whole-20261011-c06/release-phase3-canonical-preparation/attempt3-test-runner-failure/`.
- Log SHA256: `910591be966afad2d51851ef2d404606df1b7d483d373a82325fab1c8f88d1c3`.
- Failing IR: `/home/yoon/dev/simple-release-phase3-20261011/build/native_cache/sa9790020ea899e953ed792b2054f5e74/simple-aot-diagnostic-e7Bqlo/message.module.ll`, function starts at line 481; invalid GEP at line 669.
- `message.module.ll` is a diagnostic basename, not the source module name.
- Independent void-to-i64 `cleanup_and_exit` failures and empty-MIR modules
  are separate causes and are not fixed by this candidate.

## Regression and admission

`test/unit/compiler/mir/ref_dict_index_owner_spec.spl` lowers real mutable
text-key/f64 dictionary source and requires two dictionary reads/two writes,
correct float decoding, and no array writes or GEP. Negative controls reject
Ptr(Dict), Ref(Array) and an integer as dictionary views.

`test/fixtures/compiler/ref_dict_index_owner/main.spl` exercises the original
contains/read/cache-miss/write shape, caller-visible updates, f64 compound
assignment, text and false/true values, and an array-index control. Expected
exit 0 and exact stdout `ref-dict-index-owner: pass\n`.

No compiler construction or native execution was performed in this repair
lane. Both authored regressions remain UNRUN. Admission requires coordinated
corrected-producer ARM execution plus RISC-V object validation (EM243, genuine
LLVM target) and the affected test-runner module. Keep this issue OPEN until
that evidence exists; a source review or valid object alone is not a runtime pass.
