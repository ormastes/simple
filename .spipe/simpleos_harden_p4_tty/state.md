# Lane P4 (Services/TTY) — Production Harden — state

## Goal
Master plan §1 / parallel-lane table P4: `tty_write()` returned an accepted
byte count without ever delivering the bytes to a real output
endpoint/queue — a subsequent read of the output path saw nothing. Fix the
smallest real delivery: append written bytes to a real output queue that
the console/serial reader drains, so a write is observable by a subsequent
read. Prove it with an exact-byte-content spec.

## Old defect — exact location
`src/os/services/tty_service.spl`, `tty_write` (was lines 264-273 before this
change, method body only 8 lines):

```
me tty_write(tty: Entity, bytes: [u8]) -> i32:
    val sink_slot = self.world.output_sinks.get_slot(tty)
    if sink_slot < 0:
        return -1
    bytes.len() as i32
```

It checked that the output sink *exists*, then just echoed
`bytes.len()` back as an "accepted" count. No byte ever touched any queue,
buffer, or sink — nothing a reader could later drain.

## Fix
- Added `struct OutputBuf: bytes: [u8]` component + `output_bufs:
  ComponentStore<OutputBuf>` column on `TtyWorld` (`src/os/services/tty_service.spl`).
- `tty_create` now also seeds an empty `OutputBuf` for every new TTY entity.
- `tty_write` (now ~line 276) appends the written bytes onto the entity's
  `OutputBuf` and returns the delivered count.
- New `tty_read_output(tty) -> [u8]` (now ~line 310) drains `OutputBuf` and
  returns what was written since the last drain (empty array if none / TTY
  unknown) — this is the "subsequent read of the output path".

## Root-cause landmine found while wiring this up (important — read before extending)
`ComponentStore<T>` and `TtyWorld` are plain `struct`s (value types), and
`TtyService.world: TtyWorld` is a struct field on the `class`. Calling a
mutating method **two struct-field hops** deep from `self` —
`self.world.output_bufs.insert(...)` — silently does **not** persist under
the current runtime (`build/native_probe/simple`, self-hosted, no seed
warning). The insert runs against a transient copy of `output_bufs`
produced by resolving the `self.world.output_bufs` chain as the method
receiver; the mutated copy is discarded when `insert` returns.

Reproduced in isolation (minimal repro, not committed, kept in
`/tmp/p4lane/probe_nested.spl` during this session): a `class Svc { world:
World }` / `struct World { foos: ComponentStore<Foo> }` pair where
`self.world.foos.insert(...)` never shows up in
`svc.world.foos.get_slot(...)` afterward. One-hop (`class Svc { foos:
ComponentStore<Foo> }`, `self.foos.insert(...)`) works fine. Making the
middle struct (`World`) a `class` instead of `struct` did **not** fix it —
so it isn't a struct-vs-class value-semantics issue at that layer, it's
specifically about the receiver-resolution of a chained method call two
hops deep.

**Workaround used (in `tty_write`, `tty_read_output`, and the
`output_sinks`/`output_bufs` inserts inside `tty_create`)**: extract the
store into a local `var`, mutate that, then write it back explicitly:
```
var buf_store = self.world.output_bufs
buf_store.insert(tty, OutputBuf(bytes: new_bytes), t)
self.world.output_bufs = buf_store
```
This is the same "assign-back" shape as the documented array-value-type
landmine (`arr = arr.push(v)`), just one level up the object graph.

**This same defect already existed, unfixed, before this change**, in
every other two-hop `self.world.<store>.insert(...)` call in this file:
`line_bufs` (tty_create, tty_input_char), `termios` (tty_create,
tty_set_termios), `fg_pgids` (tty_create, tty_set_fg_pgid),
`input_sources` (tty_create), `kinds` (tty_create). Confirmed by running
the pre-existing `test/01_unit/os/services/tty_service_spec.spl` against
the unmodified file on `build/native_probe/simple`: entity-creation,
termios round-trip, canonical/raw input, VINTR signal, PTY-pair, and
fg_pgid/count groups all failed there too (e.g. `tty_create` itself
returns an entity whose `kinds` slot never resolves — "index is -1"),
**independent of my change** (verified by diffing against
`git show HEAD:src/os/services/tty_service.spl` and re-running). I did
**not** fix those other call sites — out of this bounded increment's scope
(the assigned defect is tty_write delivery only) — see "Next increments"
below.

## Spec
`test/01_unit/os/tty/tty_write_delivery_spec.spl` (new). 4 examples:
1. `tty_write("hello")` then `tty_read_output` returns the exact bytes
   `[104,101,108,108,111]`; accepted count == delivered count (absolute
   content oracle, not just a length check).
2. Draining is destructive — a second read after drain returns empty.
3. Multiple writes before a drain accumulate in order.
4. `tty_read_output` on an unknown entity returns empty (no crash).

No PTY pair master-write -> slave-read round-trip test: `TtyService` has
no endpoint->entity routing table (master/slave only share a numeric
`endpoint: u64` id in `OutputSink`/`InputSource`; nothing maps that id back
to an `Entity`). Writing to the master's own `tty_write` only reaches the
master's own `OutputBuf`, not the slave's. Recorded here as the next
increment per the task instructions, not silently skipped.

## Spec verdict
Binary: `build/native_probe/simple` (self-hosted, no seed warning — the
task-recipe binaries `bin/release/x86_64-unknown-linux-gnu/simple` and
`src/compiler_rust/target/bootstrap/simple` are both stale bootstrap
seeds and print the seed warning banner; `build/native_probe/simple` is
the one clean self-hosted binary found in the tree during this session).

```
$ build/native_probe/simple run test/01_unit/os/tty/tty_write_delivery_spec.spl
TtyService tty_write real delivery
  ✓ delivers the exact bytes written through tty_write to tty_read_output
  ✓ drains destructively — a second read sees nothing new
  ✓ accumulates bytes across multiple writes in order before a drain
  ✓ tty_read_output returns empty for an unknown entity

4 examples, 0 failures
```

Fail-once proof done: temporarily reverted `tty_write` to the old
accepted-count-only body (no `OutputBuf` append) → reran the same spec →
`4 examples, 3 failures` (`array index out of bounds: index is 0 but
length is 0` on the drained-but-empty output, and a falsy "second read"
check) → restored the fix → back to `4 examples, 0 failures`.

Regression check: pre-existing `test/01_unit/os/services/tty_service_spec.spl`
group "TtyService tty_write" (2 examples: "returns byte count for valid
TTY", "returns -1 for unknown entity") — both still pass after this change
(also passed before; unaffected). Other pre-existing groups in that file
(entity creation, termios, canonical/raw input, VINTR, PTY pair,
fg_pgid/count) are unchanged — still failing exactly as they did before my
change, for the pre-existing two-hop-mutation reason above, not because of
anything I touched.

## Blockers / next increments
1. **PTY master-write -> slave-read round-trip** — needs an
   endpoint->entity (or direct entity-to-entity) routing layer in
   `TtyService` so writing to a master's output actually lands in the
   linked slave's readable queue (and vice versa). Not attempted this
   increment; `OutputSink`/`InputSource` currently only carry an opaque
   `u64` endpoint id with no lookup back to an `Entity`.
2. **Systemic two-hop chained-mutating-method-call defect** (see above) —
   affects every `self.world.<store>.insert(...)` in this file outside the
   two I fixed (`output_sinks`, `output_bufs`), and very likely affects
   every other ECS-based SimpleOS service built on the same
   `struct World { ComponentStore<T> ... }` pattern (procfs, sched,
   pipefs, rs, database services all live next to `tty_service.spl` in
   `src/os/services/` and look structurally identical). This is a runtime/
   interpreter-level defect, not a TTY-specific one, and lives outside my
   exclusive path (`src/lib/*/ecs/component_store.spl`,
   `src/lib/*/ecs/world.spl` are shared infra, not TTY/PTY sources under
   `src/os/`). Recommend filing as a standalone bug and, if fixed at the
   language/runtime level, retiring the extract-mutate-writeback
   workaround here and in every other affected service.
3. Only `output_sinks` and `output_bufs` inserts in `tty_create` got the
   writeback fix (needed for `tty_write`/`tty_read_output` to work at
   all). `line_bufs`/`termios`/`fg_pgids`/`input_sources`/`kinds` in
   `tty_create` and their respective setter/reader methods elsewhere in
   this file still use the broken direct-call form and were left alone —
   fixing them is straightforward (same pattern) but is functionally
   unrelated to the tty_write delivery defect this increment targets.

## Files touched
- `src/os/services/tty_service.spl` (modified) — `OutputBuf`
  struct + `output_bufs` column, `tty_create` wiring, `tty_write` real
  delivery, new `tty_read_output`.
- `test/01_unit/os/tty/tty_write_delivery_spec.spl` (new).
- `.spipe/simpleos_harden_p4_tty/state.md` (this file).

Not committed / not pushed per lane instructions.
