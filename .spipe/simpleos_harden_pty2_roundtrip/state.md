# Lane PTY2 (PTY master/slave round-trip — P4 increment 2) — state

## Goal
Master plan §10.1 (`doc/01_research/domain/simpleos_production_host_master_plan.md`
lines 249-255): ttyd owns PTY allocation; "PTY data path must use real shared
buffers or pipe endpoints (master write -> slave input queue -> shell read;
and reverse)". P4 (`.spipe/simpleos_harden_p4_tty/state.md`) fixed `tty_write`
delivery but explicitly deferred this round-trip: "no endpoint->entity routing
table (master/slave only share a numeric `endpoint: u64` id in
`OutputSink`/`InputSource`; nothing maps that id back to an `Entity`)".

## Queue model added
`src/os/services/tty_service.spl`:
- `struct InputBuf: bytes: [u8]` — per-entity input queue, symmetric to P4's
  `OutputBuf`. Seeded empty for every TTY entity in `tty_create` (same
  extract-mutate-writeback pattern P4 used for `output_bufs`).
- `struct PtyPair: master: Entity, slave: Entity` — the routing layer P4 found
  missing. Stored in a new `pty_pairs: ComponentStore<PtyPair>` column on
  `TtyWorld`, keyed by the MASTER entity's id. `tty_create_pty_pair` inserts
  one `PtyPair` per pair it creates.
- `tty_write_input(tty, bytes) -> i32` / `tty_read_input(tty) -> [u8]` — raw
  queue write/drain on `InputBuf`, mirroring `tty_write`/`tty_read_output`.
- `pty_master_write(master, bytes) -> i32` — looks up the `PtyPair` keyed by
  `master`, appends to the linked SLAVE's `InputBuf` via `tty_write_input`.
  This is "master write -> slave input queue"; the shell reads it back via
  `tty_read_input(slave)` ("shell read").
- `pty_slave_write(slave, bytes) -> i32` — thin named wrapper around the
  existing `tty_write(slave, bytes)` (writes to the slave's own `OutputBuf`).
  This is "shell write -> slave output queue".
- `pty_master_read(master) -> [u8]` — looks up the `PtyPair` keyed by
  `master`, drains the linked SLAVE's `OutputBuf` via `tty_read_output`. This
  is "-> PTY master read", closing the reverse direction.

Design choice: `pty_master_write`/`pty_master_read` take the MASTER `Entity`
directly (not a struct literal) and resolve the pair via the `pty_pairs`
component store — this is the actual ECS "routing layer" the task and P4
both called for, not just a bag-of-fields helper. `tty_create_pty_pair`'s
existing `(Entity, Entity)` tuple return signature was left untouched
(callers outside my exclusive path — `test/01_unit/os/services/tty_service_spec.spl`
and the two other copies under `test/unit/...` — destructure it as `pair.0`/
`pair.1` and are not in my exclusive-path list to edit).

## Root-cause landmine found while wiring this up (new — not in P4's notes)
P4's write-up documents the two-hop chained-mutating-method-call defect for
`ComponentStore.insert()` (`self.world.<store>.insert(...)` silently
discards). While building the cross-talk oracle (two independent PTY pairs
in one `TtyService`), I hit the **same defect one layer deeper**: `tty_create`
called `self.world.base.spawn()` — also a two-hop chained *mutating* method
call (`spawn()` mutates `WorldBase.alloc: EntityAllocator` internally). Every
entity spawned this way silently came back as `Entity(id: 0, generation: 1)`
— **the same entity, every time**, once a `TtyService` created more than one
TTY. P4's specs never hit this because every P4 example creates exactly one
TTY per fresh `TtyService`, so the collision never manifested — single-entity
worlds are indistinguishable from a broken allocator. My cross-talk test
creates 4 entities in one `TtyService` (two pairs), which is what exposed it:
observed `master_a id=0 slave_a id=0 master_b id=0 slave_b id=0` in an
isolated debug script before the fix.

Fix (in `tty_create`, `src/os/services/tty_service.spl`): the same
extract-mutate-writeback pattern P4 established, one level up:
```
var base = self.world.base
val e = base.spawn()
self.world.base = base
```
After the fix, the same debug script printed distinct ids
`master_a=0 slave_a=1 master_b=2 slave_b=3`. This is out-of-scope to fix at
the root (`src/lib/*/ecs/world.spl` is shared infra, not under
`src/os/services/`), same as P4's finding — flagging it here so whoever picks
up the "systemic two-hop chained-mutating-method-call defect" bug (P4's next
increment #2) knows `WorldBase.spawn()`/`despawn()` are affected too, not
just `ComponentStore.insert()`.

## Spec
`test/01_unit/os/tty/pty_roundtrip_spec.spl` (new). 5 examples:
1. Master write ("hello") -> exact-byte slave read via `tty_read_input`;
   accepted count == delivered count; second drain returns empty (consumed).
2. Slave write ("world") -> exact-byte master read via `pty_master_read`;
   accepted count == delivered count; second drain returns empty (consumed).
3. Cross-talk negative oracle: two independent pairs (A, B) each write
   distinct 4-byte payloads in both directions; A's slave/master never see
   B's bytes and vice versa (absolute per-byte assertions both ways).
4. `pty_master_write` returns -1 for a plain (non-PTY-master) entity.
5. `pty_master_read` returns empty for a plain (non-PTY-master) entity.

## Spec verdict
Binary: `build/native_probe/simple` (self-hosted, no seed warning — matches
P4's binary choice; the recipe binaries under `bin/release/.../simple` and
`src/compiler_rust/target/bootstrap/simple` are stale bootstrap seeds).

```
$ build/native_probe/simple run test/01_unit/os/tty/pty_roundtrip_spec.spl
TtyService PTY master/slave round-trip
  ✓ master write delivers exact bytes to slave read (shell read)
  ✓ slave write delivers exact bytes to master read (reverse direction)
  ✓ cross-talk is impossible between two independent PTY pairs
  ✓ pty_master_write returns -1 for an entity that is not a PTY master
  ✓ pty_master_read returns empty for an entity that is not a PTY master

5 examples, 0 failures
```

### Fail-once proof (observed, then restored)
Temporarily reverted `pty_master_write` to skip the slave-`InputBuf` append
and just `return bytes.len() as i32` (re-introducing exactly P4's original
"accepted-count-only, no delivery" defect, one level up the PTY chain):

```
TtyService PTY master/slave round-trip
  ✗ master write delivers exact bytes to slave read (shell read)
    semantic: array index out of bounds: index is 0 but length is 0
  ✓ slave write delivers exact bytes to master read (reverse direction)
  ✗ cross-talk is impossible between two independent PTY pairs
    semantic: array index out of bounds: index is 0 but length is 0

5 examples, 2 failures
```
Both failures land on the exact-content oracles (indexing into an
empty-because-never-delivered array), exactly as expected — the reverse
direction (`pty_slave_write`/`pty_master_read`, untouched by this
regression) stayed green, correctly isolating the fault to the direction I
broke. Restored the real implementation afterward; reran — back to
`5 examples, 0 failures` (shown above, "Spec verdict" section).

## P4 regression: `test/01_unit/os/tty/tty_write_delivery_spec.spl`
- **Before** (immediately after adding the `InputBuf` struct/column/seeding
  to `tty_create`, before adding any PTY-routing methods):
  `4 examples, 0 failures`.
- **After** (final state, all PTY2 code in place, `spawn()` fix included):
  `4 examples, 0 failures`.
No regression. P4's spec was already green going in and stayed green
throughout.

## Blockers
- No live shell/QEMU evidence — this is a pure in-process ECS model, no
  process, no PTY device node, no real fd, no terminal driver wired to
  hardware or a QEMU guest. Per the task's bounded scope ("pure model — no
  QEMU"), this is expected, not silently omitted.
- `PtyPair` is only keyed by the master entity id, not the slave — there is
  no reverse lookup ("given a slave, find its master/pair") yet. Not needed
  by anything in this increment; would matter for e.g. a slave-side ioctl
  that needs to signal its controlling master.
- The systemic two-hop chained-mutating-method-call defect (P4's, now
  confirmed to also hit `WorldBase.spawn()`/`despawn()`) is still unfixed at
  the root. Every call site in this file that needs a mutation more than one
  field-hop from `self` must keep using the extract-mutate-writeback
  workaround by hand until that lands.

## Next increment
Termios line discipline across the PTY boundary, and controlling-terminal /
session ownership, per master plan §10.1 ("controlling terminal, session +
foreground pgroup, SIGINT/SIGTSTP/SIGHUP/SIGWINCH, winsize"). Concretely:
route `tty_input_char`'s line-discipline processing (canonical mode, VINTR,
echo) through the PTY master->slave path so raw bytes written to the master
are processed by the slave's `Termios` before landing in `LineBuf`/
`InputBuf` (today `pty_master_write` bypasses line discipline entirely and
appends raw bytes straight to `InputBuf`), and wire `ForegroundPgid` /
session ownership so `SIGINT` delivery (already implemented for a single TTY
in `tty_input_char`) works correctly across a PTY pair.

## Files touched
- `src/os/services/tty_service.spl` (modified) — `InputBuf` + `PtyPair`
  structs, `input_bufs` + `pty_pairs` columns, `tty_create` seeding +
  `spawn()` writeback fix, `tty_write_input`/`tty_read_input`,
  `pty_master_write`/`pty_slave_write`/`pty_master_read`,
  `tty_create_pty_pair` wiring the `PtyPair` component.
- `test/01_unit/os/tty/pty_roundtrip_spec.spl` (new).
- `.spipe/simpleos_harden_pty2_roundtrip/state.md` (this file).

Not committed / not pushed per lane instructions.
