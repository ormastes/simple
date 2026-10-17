# Windows Stage 2 treats a single AST expression payload as a tuple

Status: owner repair authored; rebuilt-producer execution pending.

The rejected edc32fa producer SHA256
`6e0a096c5cb5433270e30006ac2b304337c5ecb753abc91a9b71f3c46c69b16f`
passed the cache-enabled p2_add gate. Its stage2-mir-retention admission build
then failed with a HIR worker access violation. The fixture contains only
`fn main(): print("abc".len())`; it imports no compiler modules.

One CDB capture on 2026-10-18 retained `retention-av.dmp`, `cdb.log`, the bounded
collector receipt, RSS observer receipt, exact-object mapping, and disassembly
under `D:/dev/simple-smux-next-20261017/build/smux-astra-oct18/retention-cdb`.
The timeout was 180 seconds; observed aggregate RSS peaked at 3,490,484,224
bytes below the exact 6,000,000,000-byte RSS limit. The RSS observer started
after launch; the collector also imposed a 6,227,702,579-byte job commit cap.
Capture processes were quiescent afterward. CDB exited zero because its AV
handler quit after saving the dump; that is not a compiler PASS.

The AV was `mov r14,[rax]` with RAX zero at RVA `0x2b8d19`. Matching 80 bytes
outside COFF relocations identifies
`HirLowering.dynamic_callback_function_type+0xb69` in the retained
`1ff7a672bf155e1e.o`. Its callers map to `dynamic_callback_tail_type`,
`infer_untyped_return_type`, and `declared_callable_type`.
The immediately preceding calls are `rt_enum_payload` then `rt_tuple_get(0)`;
the returned word is masked with -8 and dereferenced. Source called
`_sffi_tuple_get<Expr>(rt_enum_payload(tail.kind), 0)`.

`StmtKind.Expr(Expr)` declares one direct payload. The same retained object's
probe construction passes the Expr pointer directly to `rt_enum_new`, without
a tuple allocation. The tuple projection is therefore the wrong owner-level
ABI assumption. This is separate from the earlier SymbolId dictionary evidence.
Latest baseline `68717c2989c` still contained all three affected projections;
the annotation fixes and codec-refusal fixes did not remove them.

The repair shares `hir_ast_expr_statement_payload_v1` across dynamic callback
function/parameter inference and return scanning. It retains the variant
discriminant guard, extracts the declared variant through a typed pattern,
and returns nil for absent or other-variant payloads. Multi-field If payload
projection and global runtime tuple/enum ABIs remain outside this repair.

Focused AST controls and a native entry are recorded in
`doc/06_spec/01_unit/compiler/hir/expr_statement_payload_spec.md`.
The original MIR-retention fixture remains the required regression gate.
The same producer separately compiled and ran real Hello successfully; receipts
are in `build/smux-astra-oct18/hello-build.job.env` and `hello-run.job.env` in
the NEXT worktree. That qualifies the diagnostic producer only, not this fix.
