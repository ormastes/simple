# Stage 3 MIR lowering rejects unresolved module static initializer

Status: fixed and cleared by canonical Stage 3; successor SIGSEGV recorded separately.

The latest canonical Stage 2 rebuild, after the reviewed compiler/bootstrap
performance ports, admitted compiler
`3dd3fa60b332b9197b60a7c1eaf5306f115cbe590cf8f9e40d61dbf08309fcf5`
(846 compiled, 0 cached, 0 failed). Its frozen manifest was
`42ad9b3ff4bd58a12deeb6bb5e924cad3540d60b2ba0b9e5092c04648819c6a1`
with 27,071 listed inputs verified. The subsequent single Stage 3 resume
reached all 604/604 parsed sources and HIR completion, then terminated during
MIR lowering with status 1, wall time 11:32.69, and peak RSS 14,408,012 KiB.
No candidate compiler or sanity receipt was produced.

Exact fatal diagnostic from `build/bootstrap/logs/x86_64-unknown-linux-gnu/stage3-native-build.log`:

```text
error: bootstrap MIR lowering: cannot derive module static type from unresolved initializer; add an explicit annotation
```

The emitting branch is
`src/compiler/50.mir/_MirLowering/module_lowering.spl::lower_static`, where an
inferred module static whose folded initializer is unresolved is rejected. The
current log does not identify the module or static name. Explicit annotations
on `CURRENT_SFFI_OPTS` and `CURRENT_RUST_CONFIG` did not clear this diagnostic,
so those earlier static candidates are disproven as the sole owner. The bounded
diagnostic change now includes module name, static name, and source
file/line/column in both inferred-static failure branches. Earlier aggregate-copy
SIGSEGV evidence is cleared by the Rust emitter guard; this is a distinct
successor blocker. Do not claim Stage 3 admission or Stage 4 deployment until
an attributable fix and a new admitted Stage 3 transaction succeed.

Latest retained evidence:

- Stage 2 controller: `build/native_probe/stage4-owner-20260815/canonical-stage2-perf-ports.{log,status,time}`
- Stage 3 controller: `build/native_probe/stage4-owner-20260815/canonical-stage3-perf-ports.{log,status,time}`
- Exact Stage 3 diagnostic: `build/bootstrap/logs/x86_64-unknown-linux-gnu/stage3-native-build.log`

Diagnostic-fix verification:

- `test/01_unit/compiler/mir/module_static_diagnostic_context_spec.spl`: 1/1 PASS in interpreter mode.
- All five `lower_static` call sites now pass an authoritative logical module name.
- Refreshed frozen manifest SHA-256: `caac30d41cc0f3f4836fca9ae013420cfda936bc458b16a3f2b3f06ecd8d4c6a` (27,071/27,071 verified).
- The identity-bearing canonical cycle admitted Stage 2 compiler `9c1bebdb837e6cc964008d4b71dcbc51c7b28aa664b5dd90d9439748d9dca662` (846 compiled, 0 cached, 0 failed), then reached Stage 3 parse 604/604 and HIR completion.
- Exact Stage 3 fatal: `module='compiler.frontend.core.lexer' static='current_core_lexer' source='src/compiler/frontend/core/lexer.spl:64:52'`; status 1, elapsed 12:45.67, peak RSS 14,407,412 KiB, no candidate.

The named source binding was already explicitly declared as
`var current_core_lexer: CoreLexer = make_core_lexer("")`. The parser retained
that annotation in `decl_ret_type`, but
`src/compiler/10.frontend/_FlatAstBridge/module_assembly.spl` discarded every
module val/var type tag by constructing `ParserConst(has_type_: false,
type_: Infer)`. The bounded fix now converts `decl_get_ret_type(idx)`, preserves
`has_type_` and the concrete `Type` in `ParserConst`, and reuses that same type
for synthetic script bindings. Untyped bindings remain explicitly inferred.

Focused regression
`test/01_unit/compiler/frontend/flat_fixed_type_tag_protocol_spec.spl` passes
3/3, including typed `CoreLexer` and untyped sibling cases. Frozen manifest
SHA-256 is
`d00887e50546aec288627f2f97033979b73287b269e09ec79e0c95dba59c6140`
(27,071/27,071 verified). The following Stage 2 transaction admitted compiler
`2344e9c8d0481616942f2d0301aa847ec52e6df2aabd01472877ac0f22bcb255`
(4 compiled, 842 cached, 0 failed; sanity and receiver gates PASS).

That compiler cleared `current_core_lexer`, reached Stage 3 parse 604/604 and
HIR completion, then exited 1 after 12:10.77 with peak RSS 15,205,800 KiB.
The next exact fatal was:

```text
error: bootstrap MIR lowering: cannot derive module static type from unresolved initializer: module='compiler.frontend.core.aop_debug_log' static='_expr_13' source='src/compiler/frontend/core/aop_debug_log.spl:62:11'; add an explicit annotation
```

`_expr_13` is the Flat-AST sentinel for the bare top-level `_auto_init()` call,
not a value-bearing module static. The third bounded fix recognizes only
`_expr_` names with a nonempty decimal suffix, keeps each expression in the
ordered dynamic module initializer, and skips static type derivation,
`MirStatic`, and `StoreGlobal` creation after lowering its side effect. An
ordinary call-initialized module binding remains unchanged. The focused
parser-to-HIR-to-MIR regression
`test/01_unit/compiler/mir/module_top_level_expr_initializer_spec.spl` passes
1/1: the inferred-Unit top-level call produces zero static/store entries, the
ordinary typed global produces one of each, and the initializer retains both
calls exactly once.

This is containment for the existing `_expr_N` sentinel contract. The broader
script-versus-imported-module bridge heuristic and the noncanonical direct
`MirLowering.lower_module` bootstrap branch still need separate ownership; the
canonical flat Stage 3 path uses `bootstrap_lower_to_mir_context` and does call
`lower_runtime_module_initializers_named`. No Stage 3 candidate exists yet.
Per the three-cycle cap, exactly one final Stage 2 admission and one Stage 3
retry may verify this batch; any successor blocker must be reported without a
fourth fix cycle.

Final verification admitted Stage 2 compiler
`042b35c2ef8c2f74f2b1f2497ba2c8acd3830e035cccdc3a6feac342b3ba5844`
(846 compiled, 0 cached, 0 failed; sanity and receiver PASS). Its Stage 3 run
completed parse 604/604 and HIR without repeating either the
`current_core_lexer` or `_expr_13` fatal. The unresolved-static category is
therefore cleared. The run later terminated with SIGSEGV 139 during MIR; that
distinct successor is tracked in
`stage3_mir_runtime_error_trace_segv_2026-08-15.md`. No Stage 3 candidate was
produced.

The bounded annotation retry rebuilt Stage 2 successfully (same admitted SHA) and then reached parse 604/604 plus HIR completion before terminating with SIGSEGV status 139. It consumed 641.68s user / 45.41s system and peaked at 14,191,028 KiB RSS. Its native log contained no fatal diagnostic or retained instruction pointer, so the unresolved-static hypothesis is not confirmed by that run; no candidate or Stage 3 receipt exists.
