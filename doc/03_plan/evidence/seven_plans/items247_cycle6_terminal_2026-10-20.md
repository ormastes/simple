# Final authorized cycle 6: terminal failure

STATUS: FAIL. No Phase 3 PASS; no fixes landed or pushed.

Frozen source: e4049c1437b1eb47311e5299b29dd27824567013.
Admitted producer: e5434790d2374ca667f3e8432e439016d091336829883ed17db65e62cb70548c.
Source snapshot: a29bec24101deb4a07dd01702a9ddc80739b67785b1317f438788f44d64744f6.
Base release_phase3: d9e177de79ac599ecd4b165e39c26d99f037c357.

Phase 2 compiled1401 modules without failures (423.5s compile+20.3s link),
linked and passed both frontend sanity modes, Hello World and receiver/runtime
capability admission. This is admission evidence, not full compiler qualification.

The expanded imported-record native fixture compiled successfully, then exited22.
Checks28–30 (specific direct construction/literal fields),31 (literal equality)
and18–21 passed first. The failure compares records differing only in marker:
plain_same(prefix17,value1,marker55; prefix17,value1,marker66) returns true.
Constructor/read checks for the tested records now pass, but this does not
establish complete parameter or comparison behavior. The compile collector
proved quiescence; producer, input pins, binary/log hashes and actual exit22
are retained in build/native_probe/imported-inequality-cycle6-<producer>/.

Independent read-only review and root source inspection identified the Named
Struct parameter path in _MirLowering/function_lowering.spl: it keeps the bare
parameter_type.name, whereas Class is qualified. Plain value parameters call
copy_struct_value_recursive with that name. The copy helper in
mir_lowering_stmts.spl iterates that row's field count and reconstructs that
many operands, then records bare provenance without transferring the local HIR
note. The other provider's two-field ImportedModulo row can truncate the
correctly constructed three-field record. This explains the lost-marker shape.
Whether the later comparison recovers only two fields or reads a third field
beyond that copy remains unproved; no memory-safety PASS is claimed.

All owned qualification scopes and the separate store collector were stopped.
Their final tool handles returned terminal statuses, kernel scopes are inactive,
and the store collector receipt reports interrupted/143/quiescent=1. No store
runtime acceptance was executed. All caches remain retained.

The first provisional Phase3 launcher hit a publication-readiness race before
creating a compile/cache. Its log is preserved. A bounded readiness check then
allowed the isolated diagnostic to start; it was stopped after the runtime
counterexample and produced no qualified Phase3 artifact. No normal gate was
weakened and no admission is inferred from that diagnostic.

The user-authorized six-cycle limit is exhausted. No parameter-copy source
correction or seventh repair/build cycle was attempted. Continued repair needs
a changed user limit. Existing scope remains intact: item2's atomic merge/split
integration and complete durable oracles; item4's positive RV64 relaxation/
dynamic and RV32 driver work plus host contracts; item7's attributed-profile
join to typed MIR/storage/artifact and broader generic physical consumers;
source-matched Stage4, system/manual evidence and required core/MCP/LSP checks.
Merged implementations and narrow probes are not whole-feature completion.
