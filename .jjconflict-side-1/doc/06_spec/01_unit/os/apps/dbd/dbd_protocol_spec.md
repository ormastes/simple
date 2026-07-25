# dbd protocol + durability (Lane C2)

> Proves the in-guest db daemon's protocol/journal/replay logic in-process,

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 12 | 12 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# dbd protocol + durability (Lane C2)

Proves the in-guest db daemon's protocol/journal/replay logic in-process,

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/apps/dbd/dbd_protocol_spec.spl` |
| Updated | 2026-07-19 |
| Generator | `simple spipe-docgen` (Simple) |

Proves the in-guest db daemon's protocol/journal/replay logic in-process,
without a socket or a mounted disk, by driving the pure seam
(src/os/apps/dbd/dbd_protocol.spl) that the freestanding transport
(src/os/apps/dbd/dbd.spl) sits on top of.

The db engine itself is the REAL Simple RESP server
(std.nogc_sync_mut.redis.server.RedisServer) — the same engine
src/app/redis_server/main.spl runs hosted. These specs assert the durability
seam this lane adds: a write-ahead journal of mutating commands that,
replayed through that same RedisServer.dispatch(), reconstructs the store —
which is exactly the reboot-persistence guarantee (write journal, read it
back after reboot, replay).

## Scenarios

### dbd protocol: mutation classification

#### SET and DEL are mutating (case-insensitive)

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(dbd_command_is_mutating("SET")).to_equal(true)
expect(dbd_command_is_mutating("DEL")).to_equal(true)
expect(dbd_command_is_mutating("set")).to_equal(true)
expect(dbd_command_is_mutating("del")).to_equal(true)
```

</details>

#### reads are not mutating

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(dbd_command_is_mutating("GET")).to_equal(false)
expect(dbd_command_is_mutating("PING")).to_equal(false)
expect(dbd_command_is_mutating("EXISTS")).to_equal(false)
```

</details>

### dbd protocol: journal encode/decode round-trip

#### encodes args as a space-joined line

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(dbd_encode_journal_line(["SET", "k", "v"])).to_equal("SET k v")
```

</details>

#### rejects args containing a space (ambiguous journal line)

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(dbd_encode_journal_line(["SET", "k", "a b"])).to_equal("")
```

</details>

#### rejects args containing a newline (ambiguous journal line)

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(dbd_encode_journal_line(["SET", "k", "a\nb"])).to_equal("")
```

</details>

#### decodes a journal line back into args

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val args = dbd_decode_journal_line("SET k v")
expect(args.len()).to_equal(3u64)
expect(args[0]).to_equal("SET")
expect(args[1]).to_equal("k")
expect(args[2]).to_equal("v")
```

</details>

#### encode then decode is an identity for well-formed args

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val encoded = dbd_encode_journal_line(["DEL", "mykey"])
val decoded = dbd_decode_journal_line(encoded)
expect(decoded.len()).to_equal(2u64)
expect(decoded[0]).to_equal("DEL")
expect(decoded[1]).to_equal("mykey")
```

</details>

### dbd engine: real RESP dispatch

#### SET then GET returns the value via the real engine

- var eng = DbdEngine new
   - Expected: eng.dispatch(["SET", "k", "v"]) equals `+OK\r\n`
   - Expected: eng.dispatch(["GET", "k"]) equals `$1\r\nv\r\n`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var eng = DbdEngine.new()
expect(eng.dispatch(["SET", "k", "v"])).to_equal("+OK\r\n")
expect(eng.dispatch(["GET", "k"])).to_equal("$1\r\nv\r\n")
```

</details>

#### GET on an unknown key returns RESP nil

- var eng = DbdEngine new
   - Expected: eng.dispatch(["GET", "missing"]) equals `$-1\r\n`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var eng = DbdEngine.new()
expect(eng.dispatch(["GET", "missing"])).to_equal("$-1\r\n")
```

</details>

### dbd engine: journal replay = reboot persistence

#### replaying a journal reconstructs the store through the real engine

- var eng = DbdEngine new
   - Expected: replayed equals `4i64`
   - Expected: eng.dispatch(["GET", "alpha"]) equals `$1\r\n9\r\n`
   - Expected: eng.dispatch(["GET", "beta"]) equals `$-1\r\n`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Simulate the durable journal written across a previous boot.
val journal = "SET alpha 1\nSET beta 2\nSET alpha 9\nDEL beta"
var eng = DbdEngine.new()
val replayed = eng.replay_journal(journal)
expect(replayed).to_equal(4i64)
# alpha was overwritten to 9, beta was deleted.
expect(eng.dispatch(["GET", "alpha"])).to_equal("$1\r\n9\r\n")
expect(eng.dispatch(["GET", "beta"])).to_equal("$-1\r\n")
```

</details>

#### empty journal replays nothing

- var eng = DbdEngine new
   - Expected: eng.replay_journal("") equals `0i64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var eng = DbdEngine.new()
expect(eng.replay_journal("")).to_equal(0i64)
```

</details>

#### post-replay writes coexist with replayed state (durability continuity)

- var eng = DbdEngine new
   - Expected: replayed equals `1i64`
   - Expected: eng.dispatch(["SET", "fresh", "no"]) equals `+OK\r\n`
   - Expected: eng.dispatch(["GET", "persisted"]) equals `$3\r\nyes\r\n`
   - Expected: eng.dispatch(["GET", "fresh"]) equals `$2\r\nno\r\n`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var eng = DbdEngine.new()
val replayed = eng.replay_journal("SET persisted yes")
expect(replayed).to_equal(1i64)
expect(eng.dispatch(["SET", "fresh", "no"])).to_equal("+OK\r\n")
expect(eng.dispatch(["GET", "persisted"])).to_equal("$3\r\nyes\r\n")
expect(eng.dispatch(["GET", "fresh"])).to_equal("$2\r\nno\r\n")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 12 |
| Active scenarios | 12 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
