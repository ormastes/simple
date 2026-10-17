# Match-bodied callbacks rejected by native closure analysis

Status: fixed in source only; executable regression and docgen **TEST_BLOCKED** pending a qualified compiler containing this patch. No bug database row or runtime PASS is claimed.

Requirement trace: REQ-SSPEC-COMPILER.

## Observed boundary

The Windows smux diagnostic used current source 3636b716294 with the frozen f612 producer. Its retained `build/smux-diagnostic-current/smux-build.stderr.log` reports HIR 117/117 followed by MIR 113/117 successful. Three raw Lambda failures occur in `nogc_async_mut/io/buffer.spl` at lines 166, 301, and 333, each a `match result` callback. Five unsubstituted-T errors and unresolved trait/then calls are separate unresolved causes. This repair does not claim to fix those causes or qualify smux.

Source examination independently establishes the closure-analysis defect in both compiler revisions: `lambda_body_captures` conservatively returns true for MatchCase, while `lambda_capture_scan_supported` rejects it and `collect_free_var_syms` does not visit it. Consequently the real closure lift declines these bodies.

## Owner repair

The three traversals now visit scrutinee, pattern expressions, guard, and arm block statements/value. A shared pattern descriptor recursively records binding SymbolIds and expression dependencies. Scrutinee and pattern expressions use the outer scope; each guard/body receives only its own arm bindings. Nested matches recurse. Or alternatives must carry equal canonical symbol sets. Invalid/unlowered patterns and unsupported arm expressions remain on the conservative refusal path, including when no known free variable exists.

Captured values continue through the existing runtime closure allocation, set/get, and indirect-call ABI. No closure environment, type parameter, task transfer, or dynamic trait semantics are erased. No family selection or application caller is changed.

## Pending qualification

Use a newly built, Hello-qualified Pure-Simple compiler; record executable digest, source revision, backend, runtime authority, target, options, and private cache/output directories. The frozen f612/3636 artifacts and prior receipts remain unchanged.

```text
<qualified-simple> test test/01_unit/compiler/mir/match_lambda_capture_scope_spec.spl
<qualified-simple> test test/02_integration/compiler/match_lambda_closure_conversion_spec.spl
<qualified-simple> native-build --native-backend=llvm --source src/lib --entry-closure --entry test/fixtures/compiler/native_match_lambda_capture.spl --output <private-output>/match-closure.exe
<private-output>/match-closure.exe
```

Native expected exit is 0 and stdout is `match-closure:13,8,-2,6,7,5,10,12` with the platform newline. Repeat the same fixture with the admitted Cranelift backend and interpreter according to the configured-variants guide; do not substitute Rust-seed test execution. Native external value checks distinguish actual captured values, guard-only state, arm shadowing, nested matches, scrutinee capture, and bind-time snapshots.

Unit tests assert exact free-symbol arrays, nested pattern/rest binding arrays, Or set normalization, no cross-arm leakage, and negative refusal. Parsed-source integration tests exercise real HIR binder normalization and inspect actual runtime capture calls. All scenarios are authored, unexecuted; no coverage percentage is asserted.
