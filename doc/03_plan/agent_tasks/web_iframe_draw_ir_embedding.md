# Agent tasks: Web iframe Draw IR embedding

Status: design landed; lane 1 awaits a fresh bounded docgen/runtime session

Frozen names:

- `draw_ir_embed_composition`
- `_simple_web_layout_compose_document`
- displayed SSpec steps/matrix names in the detail design
- unimplemented initial checkers use `fail(...)`

| Order | Lane | Scope | Dependency |
|---:|---|---|---|
| 1 | TDD owner | Modern SSpec/manual with basic/order/clip fail-fast controls | Runtime pending accounting landed in `7220a9aa51ef`; regenerate in a fresh session because the prior iframe docgen lane reached its three-cycle cap and Stage2 docgen still segfaults |
| 2 | Draw IR transform | Rebase offsets/IDs/clips and preserve every other command field | lane 1 |
| 3 | Web producer | Shared composer, depth/rules/deadline child insertion, and ordered child material-witness folding | lanes 1–2 |
| 4 | Engine2D evidence | Existing executor closes frozen pixel matrix | lane 3 |
| 5 | Caller migration | Five callers in frozen order; delete blit helpers last | lane 4 |
| 6 | Traceability/manual | Claim bounded support only after qualified run; zero-stub manual | lane 5 |

Parallel sidecars: `N/A` for lanes 2–5 because they share flat ordering and the
renderer owner. One read-only SSpec/manual reviewer may run beside lane 4 after
the names above are fixed.

Merge owner: primary web-browser hardening agent.

Final reviewer: normal/highest-capability agent at the merged revision. Reject
iframe IMAGE commands, `[u32]` child buffers, lost present-zero clips,
appended-out-of-order children, parent-only material evidence, external `src`
authority, or unqualified PASS.

Stop after three focused verify/fix cycles. Any parity mismatch blocks the
next migration. Any need for full bootstrap, Rust seed, new IR schema, or a
private Engine2D path stops the tranche with a concrete blocker.
