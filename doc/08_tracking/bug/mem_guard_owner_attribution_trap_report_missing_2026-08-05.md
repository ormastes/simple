# M2 guard-page trap has no owner-attribution report on either backend

**Date:** 2026-08-05
Status: OPEN (P3)
Status re-verified 2026-08-17 by source inspection (triage shard 02).
fixed" below).
**Severity:** Medium. Not a false-safety claim like the guard-row bug this
follows (`mem_infra_guard_row_false_on_native_backends_2026-07-31.md`) — the
guard page itself genuinely traps on both the Rust interpreter path
(`mem_guard.rs`) and the native-C path (`runtime_memory_guard.h`, landed
`8f3948de5ed`). What is missing is purely diagnostic: neither side prints
*who allocated the freed/overflowed slot* when the trap fires, which is the
design doc's own §2 promise ("Owner label on the trap").

## Claim vs reality

`doc/05_design/runtime/memory_analysis/m2_guard_and_harden_design.md` §2:

> **Owner label on the trap**: a `sigaction`-installed `mem_guard_fault_handler`
> (async-signal-safe: no locks/alloc) binary-searches a copy-on-grow
> `Vec<(page_base, page_end, slot_idx)>` for the faulting address and prints
> size, overflow/underflow/UAF classification, free-site if UAF, and the
> **owner name from M1** — `slot.owner` was captured at alloc time from
> `ATTR_CURRENT_OWNER` ... reuses `owner_report()`'s tab-separated format.

**MEASURED 2026-08-05** — this `sigaction`/`mem_guard_fault_handler` mechanism
does not exist on either side:

| Symbol | Rust (`interpreter_extern/mem_guard.rs`) | Native C (`runtime_memory_guard.h`) |
|---|---|---|
| `owner` captured at alloc time | **yes** — `GuardSlot.owner: u32` field, set from the `owner` arg to `guard_alloc_sampled` | **no** — `RtMemGuardSlot` has no owner field at all |
| `sigaction`/signal handler installed for the guard trap | **no** — `grep -n 'sigaction\|SIGSEGV' mem_guard.rs` → 0 hits | **no** — same, `runtime_memory_guard.h` has 0 hits |
| Owner actually read/printed anywhere on a guard fault | **no** — the field is `#[allow(dead_code)]` with the comment "read by future owner-report consumers (M2 fault report is optional here)" | **no** — no field to read |

So the "port it from the Rust/interpreter side" framing does not apply as
written: the Rust side captures an owner id per slot but never wires it to
anything at fault time (no signal handler exists to read it), and the design
doc's own signal-handler mechanism was never built on *either* side. There is
nothing working to port — both sides are equally at the "field exists,
nothing consumes it" (Rust) or "field doesn't exist" (C) stage.

## Why this is filed, not fixed here

Building the actual `mem_guard_fault_handler` is a real, independent design
piece, not a small port:

1. It requires installing a **process-wide `SIGSEGV` handler** that must
   coexist with whatever crash/backtrace handling already exists elsewhere in
   the runtime (`runtime_native.c` and the Rust seed both already touch
   `sigaction` for unrelated purposes — see `runtime_native.c:540`) without
   clobbering it, and must correctly re-raise/chain to the default handler
   for any `SIGSEGV` that is NOT a guard-page hit (every other segfault in the
   process still needs to crash normally).
2. It must be **async-signal-safe**: no `malloc`, no `Mutex` lock (the guard
   slot table itself is protected by ordinary means outside the handler,
   which is a signal-safety hazard if the handler needs to walk it), as the
   design doc explicitly calls out.
3. It needs a **binary-searchable page-range index** (`page_base, page_end,
   slot_idx`) built and kept in sync with the existing linear
   `rt_mem_guard_slots[]` scan, which is a data-structure change, not a
   one-line addition.
4. Free-site tracking for the UAF case (`free-site if UAF`) needs a
   backtrace-or-callsite capture on `rt_free`, which the current
   `RtMemGuardSlot`/`GuardSlot` structs do not record at all today.

Each of these is independently scoped work with its own correctness bar (a
signal handler bug is a much worse failure mode than a missing report — it
can turn a clean trap into a hang or a corrupted crash). Given the session's
actual scope (stale-slot and after-sweep UAF fixtures for the native guard
allocator, `rt_mem_guard_stale_slot_selfcheck.c` and
`rt_mem_guard_after_sweep_selfcheck.c`), inventing this signal-handler
mechanism here would be exactly the kind of undersized, unreviewed addition
the repo's over-engineering/no-shortcuts rules warn against.

## What already exists and is NOT affected

- The guard page itself traps correctly (both backends) — this bug is purely
  about the missing *diagnostic label*, not detection.
- The M1 owner-attribution mechanism (`note_attr_alloc`/`ATTR_CURRENT_OWNER`,
  `owner_report()`) is real and already used elsewhere (e.g.
  `rt_mem_attr_set_owner`, `memory.rs:227-257`) — it is a legitimate source to
  wire into a future fault handler, just not one it is currently wired to.

## Remains, concretely

1. Design and implement `mem_guard_fault_handler` (Rust) and its native-C
   mirror: install once, classify the fault (overflow/underflow/UAF) by
   comparing the faulting address against the tracked slot ranges, print
   size + classification + owner (Rust: already-captured `owner` field;
   native C: add the missing `owner` field to `RtMemGuardSlot` first) as a
   pre-crash diagnostic, then let the process die exactly as it would have
   without the handler (do not swallow the signal).
2. Add free-site capture to both `GuardSlot`/`RtMemGuardSlot` for the UAF
   "free-site if UAF" part of the report.
3. A fixture that asserts the printed report (via a subprocess and its
   captured stderr) contains the expected owner name, size, and
   classification — not just that the process crashed.

## Re-verification 2026-08-09

Status confirmed **ARCHITECTURAL-OPEN**. Re-ran the doc's own grep evidence:

- `/usr/bin/grep -n "sigaction\|SIGSEGV" src/compiler_rust/compiler/src/interpreter_extern/mem_guard.rs src/runtime/runtime_memory_guard.h` → 3 hits, all comments/doc-prose (`architecturally different mechanism from POSIX SIGSEGV`, `SIGSEGV the test runner by design`, `a small overflow SIGSEGVs on the guard`) — zero `sigaction(` calls, zero installed handler. Confirms the doc's claim: no signal handler exists.
- `RtMemGuardSlot` in `runtime_memory_guard.h` still has no `owner` field.

The `mem_guard_fault_handler` mechanism the design doc's §2 promises still
does not exist on either backend. Building it (process-wide `SIGSEGV`
handler, async-signal-safe page-range lookup, free-site capture) is real,
independently-scoped design/implementation work — not a bounded fix that
belongs in a bug-doc verification pass, and touching a global signal handler
without review risk is exactly the kind of undersized, unreviewed addition
the repo's rules warn against. No code changed; doc left OPEN.

## Related

- `doc/05_design/runtime/memory_analysis/m2_guard_and_harden_design.md` §2 —
  the unmet exit criterion this bug tracks.
- `doc/08_tracking/bug/mem_infra_guard_row_false_on_native_backends_2026-07-31.md`
  — the sibling bug for the guard-page mechanism itself (RESOLVED
  2026-08-02); this bug is the next unmet piece of the same design doc
  section, now that the mechanism it depends on exists on native C.
- `src/compiler_rust/compiler/src/interpreter_extern/mem_guard.rs:53-59` —
  the dead `owner` field.
- `src/runtime/runtime_memory_guard.h` — the native-C guard slot struct with
  no owner field at all.

## 2026-08-17 re-verification (lane m1_rust_interp) — STILL LIVE (confirmed by source)

Classified by CONTENT (per session CORRECTIONS #1).

`src/compiler_rust/compiler/src/interpreter_extern/mem_guard.rs` stores the owner
id but never consumes it. The struct field at :56-57 is literally annotated as
unread:

```
#[allow(dead_code)] // read by future owner-report consumers (M2 fault report is optional here)
owner: u32,
```

`guard_alloc_sampled(size, owner)` (:98) records `owner` into the guard record at
:137, and that is the only use. There is no SIGSEGV trap handler that reads it
back and no report emitter anywhere in the file.

**Status: OPEN, confirmed live.** This is a missing-feature gap (attribution
report never implemented), not a silent-wrong-result defect — a guard-page
SIGSEGV is loud, it just lands without owner attribution. Correctly scoped as P3.
Implementing it requires a trap handler outside the interpreter scope, so it was
not attempted in this lane.
