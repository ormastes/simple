# Native helper provider globals and receiver failures

Status: unresolved; regression fixture prepared, native execution pending.

The native compiler subsystem parser generator and authored-main verdict helper
both failed before code generation under producer `3bd458857152a0c1be96b08f21c87ebd686c3f155a87f0f0eb7633d1bd2b07cb`
and target source `e37658577b3279e30f1631dfcc8474d1c860511b`.
Preserved diagnostic packet: `test-builders-p23bd-hir20-1` under the Windows
restart evidence root. Its two `artifact/tools/steps/*/stderr.log` files hold
the actual failures. No source spans, main verdict ledger, generated aggregate,
or test result can be inferred from these unsuccessful helper builds.

The parser helper reports repeated provider declarations for canonical global
keys including `compiler.frontend.core.tokens::TOK_ASSIGN`, scalar `TYPE_*`
constants and `_AstExpr.nodes::asm_arm_*` arrays. The source declaration for
each sampled key appears once. The duplicate-provider guard in
`_MirLowering/provider_globals.spl` is retained: it prevents ambiguous storage
bindings and must not be bypassed merely to produce a binary.

The `helper_provider_aliases` fixture isolates two imports of the same actual
token provider through legacy `compiler.core` and canonical
`compiler.frontend.core` routes. Its three assertions preserve the declaration's
value and agreement between consumers. It tests a hypothesis; it does not yet
establish alias duplication as the root cause of the large helper failure.

The other fatal group contains unresolved `Result` and process-owner methods,
enum equality treated as a struct operator, and optional text receiver methods
in process/env facades. Importing `io.file_ops` instead of `io_runtime` cannot
remove this closure: `file_ops` imports `io_runtime` again and the canonical
frontend also imports process/env owners. Duplicated raw process externs in
app helpers are not an acceptable workaround.

A single diagnostic retry retains complete HIR metadata by setting the existing
`SIMPLE_STAGE3_STREAMING_SURFACES=0` gate. It keeps source, producer, parser,
verdict logic, 20-job capacity, parse-sharding workaround, and prior helper cache
directories. The compiler owns cache invalidation; no cache identity is forged.
This policy workaround remains unqualified until actual helper compile/run and
source-bound parser/verdict ledger validation succeed. Original failures remain
distinct evidence regardless of the retry outcome.
