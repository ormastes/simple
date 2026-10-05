# Cross-module native call results lose their declared type

Status: repaired; native bootstrap regression passes. No new Phase2 qualification.

Before-fix execution on release `c567b96d9b41338cd4855b026aacefadc9e10bb1`
reproduced the defect: the production builder compiled two modules with zero
failures, then the linked harness printed `oracle=1.25 local=1.25
cross=94798787397841` and failed. Both the independent oracle and local return
ABI control passed. The initial attempt stopped only because `llvm-ar` was
missing from PATH; that prerequisite failure is not the reproduction.

After the repair, both modules compiled with zero failures and the executed
harness printed `oracle=1.25 local=1.25 cross=1.25 float=2.25 override=7`.
The focused Cargo regression passed (one test, 8.67 seconds). The existing
ordering test filter passed all 14 tests on the repaired implementation.
Logs and enforced 5,859,375 KiB watchdog receipts are retained under
`build/item5-call-types` in the isolated Linux review checkout.
Touched-file rustfmt checking found existing baseline drift. After formatting
only the new ranges, `rustfmt-baseline-comparison.txt` records zero introduced
formatting hunks across all five Rust files (baseline counts 3, 14, 7, 0, 39).

The Linux Phase2 compiler `3658badf5c08ab0175841b8b265a1e55adab46cb674215b2dba71f0d9a63378c`
compiled the 13-case integer `to_float` fixture, but the executable failed on
zero. The application's integer cast and floating argument ABI were correct.
The compiler's own `convert_flat_expr` implementation called the text-returning
`expr_get_float`, then emitted `vcvtsi2sd` directly on that text handle when
constructing `ExprKind.FloatLit`. The neighboring local-text conversion emitted
the correct `rt_string_to_float` followed by `rt_value_as_float` calls.

The bootstrap native-project discovery already records declared result types,
and HIR resolves them in each module's own type registry. Those resolved types
were discarded before Cranelift result-register typing. Its declaration table
only knew the current MIR module, so a chained imported call could appear to
return an untyped integer register. Numeric builtin conversion then converted a
text address instead of parsing it.

The repair carries the current lowerer's resolved callable result map into
Cranelift before module declarations. Local bodies still override imported
metadata. There is no function-name exception, runtime representation change,
or source rewrite of the chained expression.

The regression uses the production native-project builder for separate provider
and consumer modules, links their emitted object archive with the real core-C
runtime, and executes a C harness. Its independent oracle parses `1.25` using
the runtime and compares against C's numeric literal; it also checks a local
text conversion, an explicitly aliased import, cross-module f64 arithmetic,
and a same-named local function with a different result type. This is
bootstrap-producer evidence, not qualification of
database, HTTP, SIMD, or a newly built Phase2 compiler. The original 13-case
Phase2 fixture remains unchanged and must pass with a repaired producer.

LLVM parity remains a separate follow-up. Its backend also maintains a result
type table, but clears that table at compile entry. A future repair must retain
per-module imported metadata across that reset and run a real LLVM-enabled
native-project regression; this Cranelift repair makes no LLVM parity claim.
