# BUG-2026-10-12-CONTEXT-COMPARISON

Status: open; source workaround prepared. Bug database reconciliation is
pending a qualified full CLI; this dated record does not claim a DB update.
Background repair owner: `/root/runner_mir_repair`, Rust seed parser dispatch.

Canonical Windows attempt11 froze source at
`36df8df31c639e19d6b4947b3e5fa8aad0c32c75`. All four Rust support builds,
C runtime admission and all five preflight checks passed. Stage2 native
discovery exited 1 at `driver_hir_pipeline_lowering.spl:186:13`:
`Unexpected token: expected expression, found NotEq`.

The original boolean tail was `context != "" and context == actual.context_digest`.
Rust parser `parser_impl/core.rs` dispatches a statement beginning with
`TokenKind::Context` to `parse_context` unless the next token is in its
identifier-use whitelist. That list lacks `NotEq`. Expression parsing already
accepts `context` as an identifier. The source workaround adds explicit
`return` immediately before the same expression, preserving its condition and
result. The annotated recovery reference identifies the intended original form.
The workaround commit remains distinct from the pending parser repair.

Preserved evidence: `C:/dev/simple-phase3-bootstrap-evidence/attempt11` and
the frozen attempt11 `build/bootstrap` tree. Stage2 peak RSS was 53,536 KiB
under the 5,859,375 KiB cap; its receipt records complete exit 1 and quiescence.
No new Simple compiler was produced or admitted, so Hello World and dependent
runner behavior did not run. The repaired classifier correctly reported this
diagnosed failure; that classifier PASS is not a bootstrap PASS.

Prevention must exercise the original comparison tail and real context DSL
syntax against the repaired Rust parser. Retire the source workaround only
after the affected fresh producer accepts the original form, required compiler
admission succeeds, and the removal is separately reviewed. A parser unit test
or fetched repair alone does not authorize retirement or Phase 3 qualification.
