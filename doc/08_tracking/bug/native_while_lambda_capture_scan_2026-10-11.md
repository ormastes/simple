# While expressions block native callback closure conversion

The unchanged `while_body_scope_spec.spl` registered through real `std.spec`
emits `E-MIR-EXPR-Lambda` with experimental native producer c486d76512b3
(source eecd0d7c0de). LLVM compilation nevertheless links an artifact; both
enumeration and execution then terminate with signal 11 after `owner_begin`,
before any cases or assertions are recorded. This is a failure, not a skip.

`lower_lambda_value` already lifts callbacks. Its three cooperating scans omit
`HirExprKind.While`: capture detection conservatively returns true, supported-
shape validation returns false, and free-variable collection omits its contents.
The lift consequently returns nil for the original callback.

The repair traverses the condition with the enclosing bindings and traverses
the body with body-local declarations added. Body declarations do not affect
the condition or enclosing scope. It extends the existing conversion only.

MIR regressions cover a no-capture callback preserving the outer `shadow = 99`
and a callback capturing `limit` in the condition plus `step` in its body,
where a body-local `limit` shadows the capture. The standalone native fixture
checks the observable results 101 and 10. At initial authoring, runtime
verification was pending a rebuilt native producer; the original experimental
producer was retained unchanged.

Evidence: `/home/yoon/dev/phase2-six-results-20261011/permanent-repair/normal-firstfile/llvm-positive/`.
The original std.spec positive and intentional negative must pass before the
restricted adapter can be removed. Full compiler/core checks remain pending.

## Native fixture evidence

The rebuilt experimental compiler
`54f23cb2274e43f781138a7c110ebcd3a421fb958337e5624d615af6a7fe9da3`
(source `6bffb3135df3e938a39f5e3dba13e62cde297ce1`) builds the unchanged
standalone fixture with both LLVM and Cranelift. Each executable checks the
callback results 101 and 10, exits 0, emits exactly `native-while-lambda-ok\n`,
and has empty stderr. The source owner and native fixture are byte-identical
to that frozen candidate. The pre-fix source owner also matches the release
owner before this isolated change; no framework or provider-map dependency is
introduced by this patch.

Receipts under
`/home/yoon/dev/phase2-six-results-20261011/permanent-repair/normal-firstfile-cycle3/`:
`llvm/while-fixture/result.json` and `cranelift/while-fixture/result.json`.
These are explicitly experimental native-fixture observations. The new MIR
unit scenarios have not separately run, the original std.spec wrapper remains
blocked by independent framework issues, and full-group/runtime admission is
not claimed. The restricted adapter must remain until that separate original
std.spec positive/negative acceptance succeeds.

## Current merge qualification

The observations above belong to their pinned historical producers and source
owners. The current release_phase3 merge retains the source repair, but its
admitted compiler/core/MCP/LSP and full Phase 3 qualification remain pending.
No historical diagnostic or experimental native fixture is a current merge PASS.
