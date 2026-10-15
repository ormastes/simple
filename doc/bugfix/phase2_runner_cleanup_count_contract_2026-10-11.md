# Admitted Phase2 runner cleanup count contract (#3077)

Historical source: a51194b96b5f5ce3fa57670bc62a15c2414388bf.
Admitted Phase2 producer: e6447d0d10f2c8ae552b67da8420a7e581a22bb55f79e4d4e4d30b981f095811.
Report: https://github.com/ormastes/simple/issues/3077.

Actual failure at runner_lifecycle.spl:203:11 is cleaned-count interpolation in
cleanup_and_exit, with LLVM rejecting `%l16` conversion void to i64. The callee
cleanup_all_children at line162 has no return annotation or explicit return
statement, so it is a Unit procedure despite documenting a resource count and
ending in killed+stopped. Both tracker count callees explicitly return i64.

The existing unannotated_fn_unit_return_bootstrap_spec.spl explicitly pins Unit
for an unannotated function without an explicit value-return. Thus this is a
source return-contract bug, not missing return inference. The exact fix adds
`-> i64` to cleanup_all_children. Its cleanup calls, governor accounting, logs
and final sum are unchanged. Other procedures and compiler/backend are unchanged.
No compiler-workaround annotation, fabricated zero, stub or void conversion is
appropriate; required source typing fixes the caller/callee contract.

Evidence root: release-phase3-canonical-preparation/attempt3-test-runner-failure
under phase3-whole-20261011-c06. failure.json pins log SHA
910591be966afad2d51851ef2d404606df1b7d483d373a82325fab1c8f88d1c3;
ice receipt build/ice/3814220_n7872447619908655739/ice_receipt.tsv records the
same function/span. Frozen release sources remain read-only.

## Focused qualification plan

1. With resource admission, use the exact admitted pure-Simple producer,
   SIMPLE_NO_STUB_FALLBACK=1, source/runtime before/after identity guards, a
   fresh lineage-specific cache, and monitor-only watchdog. Run the actual
   runner_lifecycle source entry through HIR/MIR/native object compilation.
2. Retain MIR/LLVM evidence that cleanup_all_children returns i64 and the
   cleaned-count use has a real i64 call result. Require actual ARM ELF ET_REL,
   symbol attribution, hash, and disassembly; declaration-only dependency
   failures must remain visible rather than being converted into success.
3. Build/run runner_cleanup_count fixture; require owned child cleanup count1,
   absent live/tracked child, repeated empty count0, exact success text and exit0.
4. Build/run runner_cleanup_exit fixture; require exit23 and formatted count0.
   Neither compilation alone nor a different status qualifies this behavior.
5. Replay the actual test_runner consumer only after focused proofs. Preserve
   other aggregate failures and do not claim complete runner qualification early.

Source review and all native/runtime proofs remain pending. No compiler launch
occurs during the disk hold. Keep #3077 OPEN until the relevant evidence lands.

## Same-class follow-up outside the admitted failing owner

`src/app/test_runner_new/runner_lifecycle.spl:134` also omits the cleanup count
return annotation and its caller consumes the count. The main runner's import
of that app-local lifecycle module is commented out at test_runner_main.spl:64;
the admitted failure identifies the active stdlib owner patched here. Record
this legacy sibling under #3077 for separate ownership/reachability review;
this patch does not claim to repair every runner implementation.
