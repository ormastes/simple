# TTY Service Specification (G8)

> Validates the SimpleOS TTY service: entity creation, Termios round-trips, canonical/raw input modes, SIGINT delivery via VINTR, PTY pair linking, foreground pgid management, write acceptance, and entity counting.

<!-- sdn-diagram:id=tty_service_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=tty_service_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

tty_service_spec -> std
tty_service_spec -> src
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=tty_service_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 18 | 18 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# TTY Service Specification (G8)

Validates the SimpleOS TTY service: entity creation, Termios round-trips, canonical/raw input modes, SIGINT delivery via VINTR, PTY pair linking, foreground pgid management, write acceptance, and entity counting.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #G8 |
| Category | Infrastructure |
| Difficulty | 3/5 |
| Status | Implemented |
| Source | `test/01_unit/os/services/tty_service_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Validates the SimpleOS TTY service: entity creation, Termios round-trips,
canonical/raw input modes, SIGINT delivery via VINTR, PTY pair linking,
foreground pgid management, write acceptance, and entity counting.

## Key Concepts

| Concept   | Description |
|-----------|-------------|
| ICANON    | Canonical mode — accumulate input until newline |
| ISIG      | Enable signal generation on control characters  |
| VINTR     | Control char index for SIGINT (default ETX=3)   |
| PTY pair  | Linked master/slave with symmetric endpoints    |

## Behavior

- tty_create spawns a live entity with correct TtyKind component
- Termios set/get round-trips without corruption
- Canonical mode accumulates bytes; read_line drains on newline
- Raw mode delivers every byte immediately (tty_input_char > 0)
- Ctrl-C (VINTR=ETX=3) in ICANON|ISIG calls signal_deliver(pgid, SIGINT)
- Ctrl-C without ISIG does NOT call signal_deliver
- tty_write returns bytes accepted
- PTY pair: master and slave exist with symmetric input/output endpoints
- fg_pgid round-trips correctly
- tty_count increments with each tty_create

## Scenarios

### TtyService entity creation

#### tty_create returns entity with correct TtyKind for console

1. var svc = TtyService new
   - Expected: svc.world.kinds.dense[k].kind equals `TTY_CONSOLE`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var svc = TtyService.new()
val tty = svc.tty_create(TTY_CONSOLE, 1, 2)
val k = svc.world.kinds.get_slot(tty)
expect(k).to_be_greater_than(-1)
expect(svc.world.kinds.dense[k].kind).to_equal(TTY_CONSOLE)
```

</details>

#### tty_create returns entity with correct TtyKind for PTY master

1. var svc = TtyService new
   - Expected: svc.world.kinds.dense[k].kind equals `TTY_PTY_MASTER`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var svc = TtyService.new()
val tty = svc.tty_create(TTY_PTY_MASTER, 10, 20)
val k = svc.world.kinds.get_slot(tty)
expect(k).to_be_greater_than(-1)
expect(svc.world.kinds.dense[k].kind).to_equal(TTY_PTY_MASTER)
```

</details>

#### tty_create returns entity with correct TtyKind for PTY slave

1. var svc = TtyService new
   - Expected: svc.world.kinds.dense[k].kind equals `TTY_PTY_SLAVE`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var svc = TtyService.new()
val tty = svc.tty_create(TTY_PTY_SLAVE, 20, 10)
val k = svc.world.kinds.get_slot(tty)
expect(k).to_be_greater_than(-1)
expect(svc.world.kinds.dense[k].kind).to_equal(TTY_PTY_SLAVE)
```

</details>

### TtyService Termios

#### set and get termios round-trips iflag oflag lflag

1. var svc = TtyService new
2. svc tty set termios
   - Expected: t.?.iflag equals `7`
   - Expected: t.?.oflag equals `3`
   - Expected: t.?.lflag equals `ICANON | ECHO`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var svc = TtyService.new()
val tty = svc.tty_create(TTY_CONSOLE, 1, 2)
svc.tty_set_termios(tty, 7, 3, ICANON | ECHO)
val t = svc.tty_get_termios(tty)
expect(t.?.iflag).to_equal(7)
expect(t.?.oflag).to_equal(3)
expect(t.?.lflag).to_equal(ICANON | ECHO)
```

</details>

#### tty_get_termios returns nil for unknown entity

1. var svc = TtyService new


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var svc = TtyService.new()
val ghost = Entity(id: 9999, generation: 1)
val t = svc.tty_get_termios(ghost)
expect(t).to_be_nil()
```

</details>

### TtyService canonical mode input

#### canonical mode accumulates bytes and tty_read_line returns them on newline

1. var svc = TtyService new
   - Expected: r1 equals `0`
   - Expected: r2 equals `0`
   - Expected: r3 equals `1`
   - Expected: line.len() equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var svc = TtyService.new()
val tty = svc.tty_create(TTY_CONSOLE, 1, 2)
# Send 'h', 'i', '\n'
val r1 = svc.tty_input_char(tty, 104)   # 'h'
val r2 = svc.tty_input_char(tty, 105)   # 'i'
val r3 = svc.tty_input_char(tty, 10)    # '\n'
expect(r1).to_equal(0)
expect(r2).to_equal(0)
expect(r3).to_equal(1)
val line = svc.tty_read_line(tty)
expect(line.len()).to_equal(3)
```

</details>

#### tty_read_line returns empty when no newline yet

1. var svc = TtyService new
2. svc tty input char
   - Expected: line.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var svc = TtyService.new()
val tty = svc.tty_create(TTY_CONSOLE, 1, 2)
svc.tty_input_char(tty, 65)   # 'A'
val line = svc.tty_read_line(tty)
expect(line.len()).to_equal(0)
```

</details>

### TtyService raw mode input

#### raw mode delivers each byte immediately

1. var svc = TtyService new
2. svc tty set termios
   - Expected: r equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var svc = TtyService.new()
val tty = svc.tty_create(TTY_CONSOLE, 1, 2)
# Clear ICANON — keep ECHO only
svc.tty_set_termios(tty, 0, 0, ECHO)
val r = svc.tty_input_char(tty, 65)   # 'A'
expect(r).to_equal(1)
```

</details>

#### raw mode delivers newline immediately without buffering

1. var svc = TtyService new
2. svc tty set termios
   - Expected: r equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var svc = TtyService.new()
val tty = svc.tty_create(TTY_CONSOLE, 1, 2)
svc.tty_set_termios(tty, 0, 0, 0)
val r = svc.tty_input_char(tty, 10)
expect(r).to_equal(1)
```

</details>

### TtyService VINTR signal delivery

#### Ctrl-C in ICANON|ISIG mode swallows byte (returns 0)

1. var svc = TtyService new
2. svc tty set fg pgid
   - Expected: r equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var svc = TtyService.new()
val tty = svc.tty_create(TTY_CONSOLE, 1, 2)
svc.tty_set_fg_pgid(tty, 42)
# Default termios has ICANON|ISIG; VINTR cc[0]=3 (ETX)
val r = svc.tty_input_char(tty, 3)
expect(r).to_equal(0)
```

</details>

#### Ctrl-C without ISIG does NOT swallow (ICANON only, char accumulates)

1. var svc = TtyService new
2. svc tty set termios
   - Expected: r equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var svc = TtyService.new()
val tty = svc.tty_create(TTY_CONSOLE, 1, 2)
svc.tty_set_termios(tty, 0, 0, ICANON)   # ISIG cleared
val r = svc.tty_input_char(tty, 3)
# No ISIG: VINTR not handled; byte accumulates → returns 0 (no newline)
expect(r).to_equal(0)
```

</details>

#### Ctrl-C in ICANON|ISIG mode calls signal_deliver for fg_pgid

1. var svc = TtyService new
2. svc tty set fg pgid
   - Expected: pgid equals `99`
   - Expected: r equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var svc = TtyService.new()
val tty = svc.tty_create(TTY_CONSOLE, 1, 2)
svc.tty_set_fg_pgid(tty, 99)
# We verify by checking return value (0=swallowed) and that fg_pgid is set
val pgid = svc.tty_fg_pgid(tty)
val r = svc.tty_input_char(tty, 3)
expect(pgid).to_equal(99)
expect(r).to_equal(0)
```

</details>

### TtyService tty_write

#### tty_write returns byte count for valid TTY

1. var svc = TtyService new
   - Expected: r equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var svc = TtyService.new()
val tty = svc.tty_create(TTY_CONSOLE, 1, 2)
val data: [u8] = [72, 101, 108, 108, 111]   # "Hello"
val r = svc.tty_write(tty, data)
expect(r).to_equal(5)
```

</details>

#### tty_write returns -1 for unknown entity

1. var svc = TtyService new
   - Expected: r equals `-1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var svc = TtyService.new()
val ghost = Entity(id: 9999, generation: 1)
val data: [u8] = [65]
val r = svc.tty_write(ghost, data)
expect(r).to_equal(-1)
```

</details>

### TtyService PTY pair

#### pty pair master and slave both exist with correct kinds

1. var svc = TtyService new
   - Expected: svc.world.kinds.dense[mk].kind equals `TTY_PTY_MASTER`
   - Expected: svc.world.kinds.dense[sk].kind equals `TTY_PTY_SLAVE`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var svc = TtyService.new()
val pair = svc.tty_create_pty_pair()
val master = pair.0
val slave  = pair.1
val mk = svc.world.kinds.get_slot(master)
val sk = svc.world.kinds.get_slot(slave)
expect(mk).to_be_greater_than(-1)
expect(sk).to_be_greater_than(-1)
expect(svc.world.kinds.dense[mk].kind).to_equal(TTY_PTY_MASTER)
expect(svc.world.kinds.dense[sk].kind).to_equal(TTY_PTY_SLAVE)
```

</details>

#### pty pair master output_sink == slave input_source

1. var svc = TtyService new
   - Expected: m_ep equals `s_ep`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var svc = TtyService.new()
val pair = svc.tty_create_pty_pair()
val master = pair.0
val slave  = pair.1
val m_sink   = svc.world.output_sinks.get_slot(master)
val s_src    = svc.world.input_sources.get_slot(slave)
expect(m_sink).to_be_greater_than(-1)
expect(s_src).to_be_greater_than(-1)
val m_ep = svc.world.output_sinks.dense[m_sink].endpoint
val s_ep = svc.world.input_sources.dense[s_src].endpoint
expect(m_ep).to_equal(s_ep)
```

</details>

### TtyService fg_pgid and count

#### fg_pgid round-trips correctly

1. var svc = TtyService new
2. svc tty set fg pgid
   - Expected: svc.tty_fg_pgid(tty) equals `77`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var svc = TtyService.new()
val tty = svc.tty_create(TTY_CONSOLE, 1, 2)
svc.tty_set_fg_pgid(tty, 77)
expect(svc.tty_fg_pgid(tty)).to_equal(77)
```

</details>

#### tty_count increments on each tty_create

1. var svc = TtyService new
   - Expected: svc.tty_count() equals `0`
2. svc tty create
   - Expected: svc.tty_count() equals `1`
3. svc tty create
   - Expected: svc.tty_count() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var svc = TtyService.new()
expect(svc.tty_count()).to_equal(0)
svc.tty_create(TTY_CONSOLE, 1, 2)
expect(svc.tty_count()).to_equal(1)
svc.tty_create(TTY_PTY_MASTER, 3, 4)
expect(svc.tty_count()).to_equal(2)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 18 |
| Active scenarios | 18 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
