# TLDR: `resource` SFFI Binding Design (2026-08-06, refreshed 2026-08-07)

- **Above everything below: no self-hosted `bin/simple` exists** (Rust seed
  has zero borrow-check code; stage-3 self-host is an open, tracked blocker)
  — none of this reaches users yet. See the plan's #0 section.
- One nominal `resource R` decl gives origin-neutral ownership: plain `R` =
  unique move-only owner with automatic release; `*R`/`@R`/`-R` = shared /
  atomic / weak per `doc/05_design/language/misc/memory.md`. No
  `Foreign<T>`/`SffiHandle<T>` in public APIs.
- Phase 1 = Grammar A: `@sffi(prefix: "rt_file", invalid: -1) resource File`
  over existing `extern fn rt_*` decls; compiler frontend parses the
  attribute; sffi_gen emits the wrapper. Phase 2 = `resource File from
  rt_file:` sugar. Phase 3 = per-function `@resource_*` attributes for
  irregular APIs.
- Name-family inference (open/create=acquire, close/free=release,
  retain/ref=retain) is scoped to the declared prefix and fail-closed —
  ambiguity is a compile error, explicit metadata always wins.
- `close()` is a consuming drop (static double-close prevention); methods
  borrow; borrowed handles are pinned alive across the extern call.
- Sigil decision: `*T` = shared ownership (memory.md wins); raw pointers get
  `raw<T>`, legal only inside generated SFFI / unsafe.
- `resource` is a **contextual/soft keyword** (declaration-position-only),
  never a hard reserved word — it's already used as an identifier in 115
  places across `src/`, including the compiler's own source.
  - Safety requires real MIR drop edges + finishing borrow-audit gap G1. G1's
  forward-propagation half is already fixed (SF1, 2026-07-28); move-**site**
  emission is partially closed as of 2026-08-07 — call-argument
  use-detection and move-emission both landed, giving `emit_move` a second
  caller — but return/reassignment/field-store/collection-store sites remain
  open (`doc/08_tracking/bug/iso_transfer_sites_missing_move_return_assign_field_2026-08-06.md`).
  The upstream parser gap is RESOLVED: `iso`/`mut` now parse in parameter
  position (2026-08-07, "LANE ISO2"); wrapper generation alone remains
  insufficient regardless.
- LANE ISO1 (2026-07-29) already landed the HIR `Isolated`/MIR `Move`
  foundation this feature builds on. The iso-struct-binding TODO
  (`mir_lowering_stmts.spl:664-672`) was attempted and reverted 2026-08-07 —
  the target branch is unreachable until `function_lowering.spl:239` unwraps
  `Isolated` before its `Named` check.
- Parallel-agent build plan (12 WPs incl. the parser-gap WP-P, Sonnet/Haiku-sized):
  `doc/03_plan/language/resource/resource_parallel_agent_plan_2026-08-06.md`.
