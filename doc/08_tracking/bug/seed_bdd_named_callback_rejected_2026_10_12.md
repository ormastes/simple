# Seed BDD dispatch rejects a named function callback

Date:2026-10-12. Status: OPEN; bug database insertionpending.

A confined d95807daf8725254e6737f12b0a81965ac5ae0a9236b19eedac94940bd9867f1 source diagnostic calls the real registry API through explicit describe(name,named_callback), matching the declared std.spec callback type fn(). The seed intercepts the BDD call and refuses the function-valued argument before executing it: `BDD block expected a block or lambda, got value; the body was not executed.`

Evidence: build/native_probe/aggregate-hook-tdd-20261012-sol/baseline3/{REQUEST.json,RESULT.json,attempt/batch.log,attempt/receipt.env}. Exit1,136 traced source reads,zero outside reads,sourcepins unchanged,final_job_active0. No real test cases or behavioral checks executed. This blocks dynamic qualification of the imported aggregate runtime's hook error handling. The prior DSL-form fixture also producedzero real registry declarations; its outer comparator lines do not establish a test PASS or hook failure.

Current source comparison (not a claim that current Rust source is identical to the immutable seed): src/compiler_rust/compiler/src/interpreter_call/bdd.rs exec_block_value at423–452 accepts Lambda,BlockClosure,Nil but rejects other values. Generic named callable support is absent in this BDD-specific path. Pure-Simple src/app/interpreter/call/dispatch.spl call_value at104 supports Value.Function and captured environments, but eval_bdd_call at351 bypasses that path and delegates BDD names to call_native. Thus ordinary function-call support alone does not establish BDD callback parity. No native pure-Simple artifact was run for this defect.

Proposed repair: dispatch legitimate named function callback values through the existing callable owner with zero arguments and preserved captured environment/error propagation. Keep noncallable values as errors and preserve pending Nil semantics, callback ordering and hook failure accounting. Mirror or unify the pure-Simple BDD call path rather than adding a success default. Required distinct TDD: named callback/lambda/block equivalence, captured value, real assertion failure propagation, real side effects exactly once, noncallable refusal, Nil pending, and before/after hook ordering.

The aggregate diagnostic's three cycles are closed; no fourth alias workaround was attempted. Its private registry guard proposal remains unverified and no aggregate runtime was imported into shared source. Six native products remain0/6; original product cases unrun.
