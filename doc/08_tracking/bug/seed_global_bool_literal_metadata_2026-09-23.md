# Seed global Boolean literal type metadata

Scoped status: HIR regression PASS. Full native coverage/default integration
remains pending in a separate lane; no Phase2/full CLI/bootstrap pass claimed.
Independent Astra review approved only this Boolean typing/test slice:
`/root/stage2_after_lexer_cleanup/coverage_metadata_review`.

## Cause and correction

The seed module registration paths inferred integer, string and array types,
but left unannotated Boolean literals as ANY for static/const/module let.
Global initializers already store raw0/1. In coverage reset, assigning a bool
to the ANY-typed inventory_enabled boxed it through rt_value_bool, while the
record-module read tested only raw0/nil3. Prior production-import disassembly
records that mismatch in `/Users/ormastes/simple-tmp/compiler-coverage-inventory-return-20260923/build/native_probe/coverage-inventory-return/reset-record-disassembly.log`.

Infer BOOL for Expr::Bool in the three registration paths, after explicit
annotations and before integer inference. This aligns reads/assignments with
the existing raw Boolean initialization convention. No coverage-specific
truthiness rule, runtime representation change or backend value sniffing.

## Focused verification

`coverage_metadata_global_bool_literals_keep_native_type` passed. It checks
module var, val, const, static and static-mut Bool types, and protects integer
11/19 from being confused with tagged Boolean values. The test body is
unchanged from the successful run; only the unrelated failing defaults test
was moved to an uncommitted file afterward.

Evidence in `/Users/ormastes/simple-tmp/coverage-global-bool-defaults-20260923/build/native_probe/coverage-global-bool-defaults/`:

- `cargo-test.log`: two tests ran; Boolean test PASS, imported-default test FAIL.
- `cargo-test.rss.env`: complete, exit101 due to the unrelated default test;
  peak3513136 KiB, sampled enforcement5859375 KiB, quiescent1.
- `cargo-check.sh`: exact private target/toolchain invocation. Final compile
  used jobs1, opt0, LTO=false, codegen-units256, debug0; verification-only.
- First two optimized one-CGU lib-test builds exceeded the unchanged memory
  cap. No test ran in those attempts. Final third cycle compiled in113s.

Runtime performance was not measured: no candidate seed native integration
was run. This adds one literal-variant comparison per module declaration and
removes accidental dynamic boxing paths; no measured speedup is claimed.
No shared/authoritative target or seed artifact was mutated. No bootstrap or
push was performed. The explicit-unit coverage prerequisite is a separate
commit (`bb75cc06519dd4c04e9b8d2fd515f59e64870825`, locally `bce81bc4224`).

## Remaining work

Imported default-argument metadata/default constant recognition is separately
unaccepted. The first direct-import regression still sees one argument where
three are required. The current source has `is_constant_default` support for
Expr::String but not Expr::FString; plain quoted-string AST classification
must be checked by the next lane. General global inference for nonliteral
expressions and cross-module global import typing is outside this literal fix.
