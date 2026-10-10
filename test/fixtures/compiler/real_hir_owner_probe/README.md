# Canonical imported unit-pattern owner regression

Status: UNEXECUTED against the proposed repair. No runtime PASS claim.

`direct_record/main.spl` is byte-identical to the real-declaration failing fixture from f3801efc1b29aecb14ba9801f6b523571f1a8ea2. It imports actual compiler HirExpr/HirExprKind and matches `expr.kind`; it is not a surrogate enum. Trace producer 98a35379112503f0b291515023c9560ffab0642fd6186b959792248e14210b1b visited this function and reported canonical/subject owner 1, local/registered owner 84, and the fixture's `[] vs [NilLit]` HIR fatal.

Fresh-producer acceptance: actual Hello object/link/run first; compile direct_record with native LLVM and ordinary isolated caches, require its HIR body completion with no binding mismatch and object emission. Dependencies must also compile; do not mask their errors or infer execution from main returning zero. Object-only is sufficient for this HIR regression; runtime execution with compiler declaration imports would require generated global initialization, never an old Hello entry.

`mismatch/main.spl` must reject the genuine payload binding mismatch `[x] vs [y]` (either order), with no emitted object. The same new producer must perform both checks. Structural SSpec additionally checks lowered owner IDs, unrelated-owner/mutable rejection, local shadow and unchanged symbol bindings; it remains UNEXECUTED until a real supported test runner is available.

Baseline/trace evidence: /mnt/c/Temp/simple-real-hir-owner-trace-evidence-20261010/first-loss.json

`object_record/main.spl` is a separate object-only variant: its typed entry parameter is forwarded to real_hir_owner_probe. Require the emitted object symbol and disassembly to retain that function's subject read/variant test (or inlined equivalent in main); a constant-return body fails this criterion. Never link/run this entry as ordinary native main: no real HirExpr argument is supplied by the platform. The original direct_record row alone supports only HIR acceptance unless retained body evidence is collected.
