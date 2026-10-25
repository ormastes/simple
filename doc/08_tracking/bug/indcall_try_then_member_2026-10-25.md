# `f(x)?.m()` is safe navigation, not try-then-member; native MIR rejects it as an unproven indirect callable

- **Date:** 2026-10-25
- **Status:** OPEN (compiler gap). Source workaround applied in the two Phase 3 modules that failed.
- **release/1.0.0:** only the `archive_file.spl` workaround is ported. `resident_cohort_seal_v1.spl` does not exist on release/1.0.0. The latent-site list below was measured at base `d3fc04205cf`; 24 of the 25 files also exist on release/1.0.0 (not `src/app/bootstrap_builder/resident_source_views.spl`) and are left unchanged there too.
- **Found in:** Phase 3 run-27e (`/home/yoon/dev/simple-boot-adhoc/build/phase3-ref/run-27e/build.log`),
  Stage 2 p2shard-17 compiler, base `d3fc04205cf`.

## Symptom

```
[go-to-end] failed stage=mir module=compiler.driver.driver_build.resident_cohort_seal_v1:
  MIR lowering error: indirect callable lacks a proven function signature at .../resident_cohort_seal_v1.spl:23:56
  (also :49:60)
[go-to-end] failed stage=mir module=compiler.backend.linker.elf.archive_file:
  MIR lowering error: indirect callable lacks a proven function signature at .../archive_file.spl:76:42
  (also :77:63, plus three cascaded "unresolved method call: substring" on `name`, lines 95/110/129 of the original file)
```

All four sites have the shape `free_fn(args)?.member(...)` (line numbers are from the original, pre-fix file):

| module | line | expression |
|---|---|---|
| resident_cohort_seal_v1 | 23 | `file_read_regular_no_follow_bounded(queue + "/inventory", 4194304)?.split("\n")` |
| resident_cohort_seal_v1 | 49 | `file_read_regular_no_follow_bounded(... ".terminal", 65536)?.split("\n")` |
| archive_file | 76 | `archive_file_ascii(header, 0, 16)?.trim()` |
| archive_file | 77 | `archive_file_decimal(archive_file_ascii(header, 48, 10)?.trim())?` |

The `substring` errors are a cascade: the failed call at :76 is replaced by
`emit_const_int(0)`, so `name` loses its `text` type. They disappear with the fix.

## Root cause

`?.` is one token (`TokenKind.QuestionDot`, `10.frontend/core/lexer_types.spl:127`) and the
language defines it as **safe navigation** (`doc/07_guide/quick_reference/syntax_quick_reference.md`
§ "Safe Navigation (`?.`)"). So `f(x)?.m()` parses as a call whose callee is
`OptionalChain(f(x), "m")` — a *field value* with no function type — not as try-`?` followed by
`.m()`. The authors meant try-then-member (Rust reading).

MIR then reaches `emit_typed_function_value_call`
(`50.mir/_MirLoweringExpr/switch_operators_calls.spl:8600`) with no declared `Function` HIR type and
no `FuncPtr` MIR type for the callee and fails closed. **The MIR check is right to reject:** it
cannot invent a signature for a field read through an optional chain. The defects are upstream:

1. The program is accepted through parse/HIR/mono with the wrong meaning (safe-nav on a `Result`
   value) and no diagnostic until MIR.
2. The MIR diagnostic names an "indirect callable", which points at function values instead of
   the `?.` spelling. Native MIR also does not support optional-chain field access at all
   (`E-MIR-EXPR-OptionalChain`, `expr_dispatch.spl:6822`), so the documented
   `result?.process()` form cannot lower natively either.

Expected fix (owner decision): either reject `?.` on a `Result`-typed base at HIR/type-check with
"did you mean `(expr?).member`", or lower `Result?.m()` as try-then-member. In both cases emit a
targeted diagnostic instead of the indirect-callable one.

## Reproduction (native, Stage 2 p2shard-17, ~50 s)

```
fn probe_word(value: text) -> Result<text, text>:
    if value == "": return Err("empty")
    Ok(value)

fn probe_free_try_method(value: text) -> Result<i64, text>:
    val trimmed = probe_word(value)?.trim()        # RED: indirect callable lacks a proven function signature
    Ok(trimmed.len())

fn probe_paren_form(value: text) -> Result<i64, text>:
    val trimmed = (probe_word(value)?).trim()      # GREEN
    Ok(trimmed.substring(1).len())
```

Measured: `holder.method(v)?.trim()`, `f(v)?.is_none()` and `f(v)?.to_string()` are all RED the
same way, so the gap is generic, not tied to text built-ins or to free functions.
`(f(v)?).m()` and `val w = f(v)?` + `w.m()` are GREEN.

## Introduced by (source side)

- `resident_cohort_seal_v1.spl`: `85ae25392df` (2026-10-21) "feat(compiler): connect resident cohort ownership to native build".
- `archive_file.spl`: `3bd31d0f528` (2026-10-03) "feat(linker): implement itemized readiness slices and real test scenarios".
- The fail-closed MIR rejection itself: `e98757b4d8e` "Repair inferred callbacks with an admitted tagged word ABI".

## Workaround (applied)

Parenthesize the try: `(f(x)?).member(...)`. Tagged `@workaround` naming this doc at each site in
the two modules. Regression guard: `test/01_unit/compiler/50.mir/try_then_member_parenthesized_spec.spl`
(interpreter-run; it pins the sites and the value semantics, not the native failure).

## Latent sites (same spelling in code, comment lines excluded; not changed)

These are outside the run-27e failing set. Some intend try-then-member, others are genuine safe
navigation on an `Option` (e.g. `70.backend/interrupt.spl:244` `...?.has_error_code() ?? false`);
both spellings reach the same unsupported native lowering, so each needs review when built natively:

- `src/app/scv/db/receipt_index_git.spl` (9)
- `src/app/bootstrap_builder/resident_source_views.spl` (5)
- `src/compiler_rust/lib/std/src/lms/server.spl` (4)
- `src/app/traceability/snapshot/git_provider.spl` (4)
- `src/app/scv/db/settlement_remote_snapshot.spl` (4)
- `src/app/scv/db/paged_import.spl` (3)
- `src/lib/nogc_async_mut/link_working_set/file_store.spl` (2)
- `src/lib/common/encoding/external_text.spl` (2)
- `src/app/scv/db/settlement_journal_git.spl` (2)
- `src/app/scv/db/checkpoint_validation.spl` (2)
- `src/os/apps/sshd/host_key_loader.spl` (1)
- `src/lib/scv/db_paged_proof.spl` (1)
- `src/lib/scv/db_paged_import_claims.spl` (1)
- `src/lib/nogc_sync_mut/debug/remote/protocol/stlink_tools.spl` (1)
- `src/compiler/80.driver/driver_managed_parse_group_main.spl` (1)
- `src/compiler/80.driver/cache/catalog/cache_catalog_projection.spl` (1)
- `src/compiler/70.backend/linker/elf/stream_inputs.spl` (1)
- `src/compiler/70.backend/interrupt.spl` (1)
- `src/compiler/50.mir/hwir/host_evaluator.spl` (1)
- `src/app/scv/db/settlement_paged_owner.spl` (1)
- `src/app/scv/db/receipt_protection.spl` (1)
- `src/app/scv/db/paged_transition.spl` (1)
- `src/app/scv/db/paged_query.spl` (1)
- `src/app/scv/db/evidence_hydrate.spl` (1)
- `src/app/scv/db/checkpoint_store.spl` (1)
