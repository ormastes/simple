# Constructor pattern placeholder context loss

Bug ID: `constructor_pattern_placeholder_context_loss_2026_10_25`.
DB registration: **PENDING qualified full CLI or canonical BugDatabase API**.
Status: **SOURCE_FIX_CANDIDATE**; native verification remains pending; not closed.

Constructor-pattern arguments were parsed without the enclosing pattern context,
allowing `_` expressions to enter ordinary placeholder-lambda rewriting. Missing
pattern tokens in the FlatAst bridge add a separate loss point in the same path.
The intended behavior retains constructor structure and placeholders as patterns.

Commit `4bbdeead3c754c7effcdec8e7537b591469e457a` scopes five parser pattern-entry
blocks with push/pop and adds bridge cases. Owners are
`core/parser_stmts.spl` and `_FlatAstBridge/convert_nodes.spl`. Structural regression:
`test/01_unit/compiler/frontend/pattern_context_placeholder_scope_spec.spl`;
native fixture: `test/04_smoke/pattern_context_placeholder_native.spl`.

Controls04 producer `c2d1992b5a75adca9cb2bb735751ef6dafe67beb9489f4ff4dc51da375c0fd63`
at source4bbdeead and controls05 producer09037 at source2a6c701 both remain failed native
attempts. Controls05 stops at HIR `unresolved name: true` at fixture42:5,
before executable assertions. That is the separately tracked while-val cause;
it does not prove the constructor repair passes.

Diagnostic source `2a6c701f680160c5871ea14a190bab26bab9e102`; native producer `09037eaa61370ee3eeceb55156cc4ff01f6c136b5ce8014dd95742f733f9bf83`; source snapshot `53182ac596bbcc4fe01d28958dc1e8fb337a5d6f6db90445c39f16f5534ee3fb`. Gen13 runtime snapshot is `ecd1ed1cbf3f68a7abc6c2f852358542fae0b6e2e66c88e5abfcd5ea22cb3d2b`. Admission and publication were not attempted.

Retained attempts: `/Users/ormastes/wt/release-phase2-review/build/verify/pattern-repair-native-controls-20261025-04/logs/pattern_context_placeholder.compile.log` and
`/Users/ormastes/wt/release-phase2-review/build/verify/pattern-repair-native-controls-20261025-05/logs/pattern_context_placeholder.compile.log`. The regression and
unchanged native fixture must pass under a new compatible producer before closure.
Ordinary nested-call placeholder scope records describe a different root.

Owner source SHA256 at `2a6c701f680160c5871ea14a190bab26bab9e102`:

- `src/compiler/10.frontend/core/parser_stmts.spl`: `2ec5e86438653e1a9942f39bafbca97c80bf5140758dd2303137480c309d117e`.
- `src/compiler/10.frontend/_FlatAstBridge/convert_nodes.spl`: `b6b2a23c41b7fbbbb2b188d64b2066d453763630b8160599036c22cb6ad771c1`.

## Final candidate code reference

The candidate is now committed at `f70df57e8f45a0ff0c8f01745d221ec61e5d4f21`, including upstream `570fc936`, Unit/while/fiber correction `ab12acf89f6`, nested legacy-Nil hardening `1d7524a6375`, pinned-generation retention `b0caa844018` and diagnostic trace cleanup `f70df57e8f4`. Earlier uncommitted descriptions and hashes above are historical snapshots; all failed native04/05, SSA and cancelled-P3 evidence remains unchanged.

Status remains **SOURCE_FIX_CANDIDATE, native verification pending, not closed**. Recorded AST diagnostic success is limited to its stated producer and assertions. DB registration remains **PENDING qualified full CLI or canonical BugDatabase API**.

Current owner source SHA256 at the final candidate commit:

- `src/compiler/10.frontend/core/parser_stmts.spl`: `872e7ede792a9517438989859a3b47aadaf570f0d8aeb2e05880bddd4fbcad3f`.
- `src/compiler/10.frontend/_FlatAstBridge/convert_nodes.spl`: `b8c18e4f26a887c6cacbcc570997380c39aae0cdfd0110be7e52d48752fdaa1b`.
