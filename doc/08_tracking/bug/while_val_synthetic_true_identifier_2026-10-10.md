# While-val introduces an unresolved synthetic true identifier

Native failure: producer 6d0b845e6e67e070f7872d8485284a247ecf27b8f4ddad168a1db7ef08fedb6b / source c9cb4ecbbd82713518a3b7cf0cf0a43f0be824cb rejects unchanged if_val_payload_owner_probe/main.spl at line22 during HIR: unresolved name true. No runtime assertion ran. Evidence: /mnt/c/Temp/simple-if-val-payload-owner-evidence-20261010/validation/optional_binding_runtime/build.log.

The simple while-val parser branch injects expr_ident("true",0), while ordinary boolean syntax and the nearby let-else loop guard use expr_bool_lit(1,0). Replacing only that synthetic condition with the real boolean node fixes its source authority without declaring a fake true variable or altering the fixture. Evaluation order, marked binding, condition refresh and break behavior are unchanged.

Status: proposed repair UNEXECUTED. Parser spec requires actual BoolLit and retained bind_optional_payload on the nested initializer. Next native criterion reruns the unchanged primitive present/absent/while/single-evaluation fixture under a newly pinned producer. The earlier invalid-array-handle diagnostic is separately retained; no causal claim ties it to this boolean node and it must not be concealed by this repair.


## Update 2026 10 25

Bug ID: `while_val_synthetic_true_identifier_2026-10-10` (reuse this report).
DB registration: **PENDING qualified full CLI or canonical BugDatabase API**;
no exact row for this ID was found in the current canonical database.
Status: **SOURCE_FIX_CANDIDATE**, native verification pending, not closed.

Controls04 (producer `c2d1992b5a75adca9cb2bb735751ef6dafe67beb9489f4ff4dc51da375c0fd63`, source4bbdeead) and controls05 retain failed attempts.
In controls05, producer `09037eaa61370ee3eeceb55156cc4ff01f6c136b5ce8014dd95742f733f9bf83`
at source `2a6c701f680160c5871ea14a190bab26bab9e102` rejects the committed pattern
fixture at42:5 with `unresolved name: true`, before runtime assertions. Raw log:
`/Users/ormastes/wt/release-phase2-review/build/verify/pattern-repair-native-controls-20261025-05/logs/pattern_context_placeholder.compile.log`.

On merged source64d0575, the applied uncommitted candidate changes only the
simple while-val synthetic condition from `expr_ident("true",0)` to
`expr_bool_lit(1,0)`. It does not create a fake binding or change fixture semantics.
The source candidate and its original native fixture remain unverified under a
new producer. The earlier2026-10-10 evidence above remains unchanged. The closed
2026-07-20 while-pattern binding report is a different cause.

Owner source SHA256 at `2a6c701f680160c5871ea14a190bab26bab9e102`:

- `src/compiler/10.frontend/core/parser_stmts.spl`: `2ec5e86438653e1a9942f39bafbca97c80bf5140758dd2303137480c309d117e`.

Applied candidate source SHA256 when recorded (uncommitted, not a qualification):

- `src/compiler/10.frontend/core/parser_stmts.spl`: `872e7ede792a9517438989859a3b47aadaf570f0d8aeb2e05880bddd4fbcad3f`.

## Final candidate code reference

The candidate is now committed at `f70df57e8f45a0ff0c8f01745d221ec61e5d4f21`, including upstream `570fc936`, Unit/while/fiber correction `ab12acf89f6`, nested legacy-Nil hardening `1d7524a6375`, pinned-generation retention `b0caa844018` and diagnostic trace cleanup `f70df57e8f4`. Earlier uncommitted descriptions and hashes above are historical snapshots; all failed native04/05, SSA and cancelled-P3 evidence remains unchanged.

Status remains **SOURCE_FIX_CANDIDATE, native verification pending, not closed**. Recorded AST diagnostic success is limited to its stated producer and assertions. DB registration remains **PENDING qualified full CLI or canonical BugDatabase API**.

Current owner source SHA256 at the final candidate commit:

- `src/compiler/10.frontend/core/parser_stmts.spl`: `872e7ede792a9517438989859a3b47aadaf570f0d8aeb2e05880bddd4fbcad3f`.
