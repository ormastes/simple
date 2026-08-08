# TLDR — Embedded Coroutine/State-Machine Research (wave-4)

- Surveyed: protothreads, stackful coroutines, C++20 frames (HALO), Rust
  async/Embassy, RTC event loops, explicit FSM, statecharts, table-driven FSM.
- Wave-3's `hil_step`/`ftl_step`/`fil_step`/`nand_step` are already
  run-to-completion — the right default — but *stateless*: no persisted
  resume-state word, so nothing external can read "what is core N doing."
- "Statement-like" debuggability = resume point stored as one named scalar
  (protothreads-with-hoisted-struct / explicit FSM), not a stack (stackful
  coroutines) or heap frame (C++20) — the only form readable from a raw
  memdump with no unwinder, which matches rv32 QEMU debugging reality here.
- Recommendation: add a **4-word `COROSTATE[0..3]` region at shm words
  254–257** (buf pool ends at 253, only 254–255 were free — 2-word budget
  bump needed, NAND state/data shift +2), named per-core state constants
  (`FTL_ST_*()` etc., fail-closed `-1` default), a pure per-core transition
  fn + a `coro_transition` driver that asserts legal-transition and emits a
  level-gated trace. Overlay only — does not change existing message logic.
- `src/lib/nogc_async_mut/coroutine.spl` already documents this exact
  discipline (state tag + saved slots + step fn) but is host-tier
  (classes/enums/closures) — not usable inside the rv32 scalar boot graph;
  relevant to the host harness only. Compiled/perf status = unverified
  ([[to be filled by lang survey]]). Suspension operator `~` is NOT
  implemented (its own spec models it without the syntax) — don't cite it.
- Full doc: `embedded_coroutine_statemachine_research.md` (this directory).
