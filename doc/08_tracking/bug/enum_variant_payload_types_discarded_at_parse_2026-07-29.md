# Enum variant payload capture is present; MC-API payload lint remains open

- **Filed:** 2026-07-29 (lane A4E `semantic-enum-payloads`)
- **Severity:** P3 — no runtime-correctness impact; the remaining issue is semantic API lint coverage.
- **Component:** compiler frontend payload capture and `semantic_api` lint integration.
- **Status:** OPEN. The parser/decl/bridge payload-loss condition described in the original report is no longer present in the current release source. This record remains open because the MC-API enum-payload lint is still not connected to the captured types. Keep it open until that remaining acceptance scope has an owner and verification.

## Original finding (historical)

The 2026-07-29 investigation correctly found that the then-current parser consumed enum payload types without retaining them, the decl arena had no payload storage, and the AST bridge emitted empty tuple payloads. Those statements describe the source snapshot investigated at that time; they are superseded by the current source findings below and must not be treated as current ground truth.

## Current release source state

Checked against current `release/1.0.0` at `232cba1b0f88272aa571d7dffe69a0a0aff8bc48`:

1. `src/compiler/10.frontend/core/_ParserDecls/enum_module_body.spl:562-584` accumulates each variant's parsed payload type tags, per-variant counts, and field names, then passes them to `decl_enum_def`.
2. `src/compiler/10.frontend/core/_Ast/decl_nodes.spl:794-846` stores payload types in `FIELD_TYPES`, counts in `FIELD_BITS`, and payload field names in `PARAM_NAMES`.
3. `src/compiler/10.frontend/_FlatAstBridge/module_assembly.spl:576-664` slices those flat lists back into variants. Named fields become `VariantKind.Struct`; positional fields become `VariantKind.Tuple`; payloadless variants remain `VariantKind.Tuple([])`.
4. `src/compiler/20.hir/hir_lowering/_Items/declaration_lowering.spl:881-887` lowers both tuple and struct payload forms.
5. The downstream gap remains: `src/compiler/35.semantics/lint/semantic_api/checker.spl:229` still has `case Enum(_): pass`, so the semantic API lint does not inspect captured enum payload types.

Current release blob IDs for the owner files are:

- enum parser: `f474cf0942d7b59703b14f90289a7d9a228ec586`
- decl arena: `9cc5c72faf9e7c9545f5b2ecd2f84440ef0aba43`
- flat AST bridge: `845487161788a88427873fe40c8fd892fa269d3d`
- HIR lowering: `cfcb4bac7f9679a182d08e6149401bbf6da4b3f5`
- semantic API checker: `c2c5a870137cfd232beaf994c05b8eb310ce3c7b`

## Regression and diagnostic evidence

PR [#5945](https://github.com/ormastes/simple/pull/5945), merged as `c00113a0dc484c7654552762d38869b1d8da891c`, corrected the existing enum payload spec contract. Its eight cases now check named field names and type order, empty tuple representation for payloadless variants, and positional tuple type order. The PR changes the spec only; it does not implement the parser capture or semantic lint.

A direct parser-owner diagnostic harness and its captured log are retained alongside this report:

- Executed harness bytes SHA256: `4A4150F78A8A7F5824C2EFA1DB63D5B4D0A59BDCC70D3143C43F8104D774DBBE`; retained LF-normalized Git blob for `test/01_unit/compiler/frontend/enum_payload_capture_direct_diagnostic.spl`: `46b701578f7c095d17be8c96d2ba0a304e7046fb`.
- Executed log bytes SHA256: `1CCD4C1FACA0A8B242216DB97D06B1FBD5D814085B8E81B53E66016A5E8DBA65`; staged retained LF-normalized Git blob for `doc/08_tracking/bug/evidence/enum_payload_capture_phase1_2026-11-02.log`: `a40328215f6a7666b19af9c6104a05a3df15b1b1`.
- Structured receipt: `doc/08_tracking/bug/evidence/enum_payload_capture_phase1_2026-11-02.sdn`

The direct run passed eight fixture scenarios: seven named/unit fixtures plus a positional `Both(i64, text)` tuple fixture. It used `C:\dev\p3new\stage2_next\seed_nilfix.exe`, SHA256 `FC56D4B5FC384EA93ED20BEFD4503FF6E27DB7734214CA45E072B4DF1B081828`. This seed is unadmitted and has no exact source-input receipt; the result is diagnostic evidence only, not Phase 2 or full-suite qualification.

The run environment set `SIMPLE_PROJECT_ROOT=C:\dev\wt\win-bootstrap-runtime`, but captured output shows imports resolving under `C:\dev\simple`. The effective enum parser blob at execution time was not independently recorded. During later review, the file in that resolved tree had Git blob `87dcec6a0a972b74faff6498e3ebc50dde00280b`; the release parser blob at that review was `47903033c383c6152a7e4ba81f1fdb9b48d92ce4`. Astra confirmed that the enum parsing body exercised by the fixtures was equivalent in those two files, while their whole-file difference was in unrelated module-script arms. The subsequent release update changed the parser file again (current blob `f474cf0942d7b59703b14f90289a7d9a228ec586`); the payload collection calls at lines 562-584 remain present. Do not describe the diagnostic as an exact whole-source release run.

The standard `test` invocation did not execute scenarios: it exited before test execution with `SDN worker scoped-environment process provider is unavailable or insufficient` (`worker_exit_code: -1`). The test-runner failure log is preserved locally at `C:\dev\wt\win-bootstrap-runtime\build\enum_payload_capture_spec_seed_nilfix_sdn.log`, SHA256 `2E409833210BF43D3E0C8DC36FDB135DA35E3DE329408E89D560404F73063861`.

## Tracking disposition

Keep this record **OPEN**. The original parser-capture condition is superseded by current source, but the linked MC-API enum-payload lint acceptance remains unsatisfied. Astra's tracking review recommends retaining the record open until the remaining lint integration has a separately reviewed owner and acceptance scope. No separate issue is created by this update.
