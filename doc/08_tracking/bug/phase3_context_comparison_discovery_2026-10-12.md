# BUG-2026-10-12-CONTEXT-COMPARISON

Status: open; source workaround prepared. Bug database reconciliation is
pending a qualified full CLI; this dated record does not claim a DB update.
Background repair owner: `/root/runner_mir_repair`, Rust seed parser dispatch.
The reviewed parser repair was integrated as `9fc4b70a52c516653fb7cf61f3e27bffb4af6370`
(exported owner commit `6e309bc3fc388cc62a736d0fafe8ddddb7aef041`).
Its bounded support baseline reproduced comparison failures; the changed-source
run passed all four actual AST regression groups, preserving context DSL
syntax. Peak RSS was 547,792 KiB and the terminal process receipt confirms
quiescence. This is Rust parser support evidence; the fresh canonical producer
still needs admission before the explicit-return workaround can be retired.

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
Workaround commit: `595121105c34159933cb5ddf20481b4122d52a97`.

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
