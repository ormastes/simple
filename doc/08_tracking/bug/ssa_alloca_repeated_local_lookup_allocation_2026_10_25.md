# SSA alloca repeated lookup allocation

Bug ID: `ssa_alloca_repeated_local_lookup_allocation_2026_10_25`.
DB registration: **PENDING qualified full CLI or canonical BugDatabase API**.
Status: **SOURCE_FIX_CANDIDATE**; native verification remains pending; not closed.

The alloca lane rescans `mir_locals` for each slotted local and linearly searches
slot keys during operand rewriting. Declared-type lookup costs O(S×L). Retained
disassembly inspection identified two eight-byte allocations per local-scan
visit. The live sample of P3 run13 showed **32.7G physical footprint** and32.9G
peak; those measurements do not attribute all memory to this lookup.

P3 run13 used source `b137e4a602b5552743d63fe09c694e21b4aafaf5` and producer
`eedc3e863bd1a925188c413bc32ed320384b05efc238eee4df71796c8cac8c37`.
The parent cancelled it for resource pressure through the owned watchdog.
Classification is **parent resource cancellation**, not compiler failure.
Evidence: `/Users/ormastes/wt/release-phase2-review/build/verify/provisional-p3-darwin-20261025-13/receipts/mir-live-sample-01.txt` and
`/Users/ormastes/wt/release-phase2-review/build/verify/provisional-p3-darwin-20261025-13/receipts/parent-resource-stop-01.json`.

Commit `4bbdeead3c754c7effcdec8e7537b591469e457a` builds first-declaration and
slot-index dictionaries once, preserving first duplicate IDs, original local
provenance, slot order, Copy/Move, spans and temporary sequencing. Original
source SHA256 was `4454eaeff42523af82d122f821011e32a54f9a4787793fb1db7195d775aa1d64`;
indexed source SHA256 `1bc11cfd21dc4493919fe7503e4d350da908b6dbbf5bd8aec672340e955b7f25`.

The Rust DDD regression at source4bbdeead executed7 examples: **2 passed, 5 failed**.
The first-index query and unchanged-local-provenance cases passed; five
transform cases reported `semantic: type mismatch: cannot convert object to int`
at the interpreter aggregate/raw ABI boundary. Preserve those failures; they
are not native SSA parity or performance evidence. Raw result:
`/Users/ormastes/wt/bootstrap-pattern-provenance-20261025/build/verify/ssa-alloca-lookup-interpreter-20261025-01/logs/spec.log`; input identities and canonical RSS receipts are alongside it.

The next criterion is a matched native comparison of retained old linear and
indexed implementations with identical inputs/checksums, elapsed and allocated
memory measurements. Plan: ignored
`build/verify/bootstrap-bug-record-preparation-20261025/ssa-native-benchmark-plan.sdn`.
No benchmark result or whole-P3 memory improvement is claimed. Existing
`llvm_constants_lost_ret_zero` database rows cover different definition/store
correctness failures and should not be repurposed for this performance root.

Owner source SHA256 at `2a6c701f680160c5871ea14a190bab26bab9e102`:

- `src/compiler/60.mir_opt/mir_opt/var_reassign_ssa.spl`: `1bc11cfd21dc4493919fe7503e4d350da908b6dbbf5bd8aec672340e955b7f25`.

## Final candidate code reference

The candidate is now committed at `f70df57e8f45a0ff0c8f01745d221ec61e5d4f21`, including upstream `570fc936`, Unit/while/fiber correction `ab12acf89f6`, nested legacy-Nil hardening `1d7524a6375`, pinned-generation retention `b0caa844018` and diagnostic trace cleanup `f70df57e8f4`. Earlier uncommitted descriptions and hashes above are historical snapshots; all failed native04/05, SSA and cancelled-P3 evidence remains unchanged.

Status remains **SOURCE_FIX_CANDIDATE, native verification pending, not closed**. Recorded AST diagnostic success is limited to its stated producer and assertions. DB registration remains **PENDING qualified full CLI or canonical BugDatabase API**.

Current owner source SHA256 at the final candidate commit:

- `src/compiler/60.mir_opt/mir_opt/var_reassign_ssa.spl`: `1bc11cfd21dc4493919fe7503e4d350da908b6dbbf5bd8aec672340e955b7f25`.
