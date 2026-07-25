# dbd protocol + durability hardening — corrupt / hostile input (Lane HARDEN-ROBUST)

> Feeds the db-daemon protocol seam (src/os/apps/dbd/dbd_protocol.spl) and the

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 16 | 16 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# dbd protocol + durability hardening — corrupt / hostile input (Lane HARDEN-ROBUST)

Feeds the db-daemon protocol seam (src/os/apps/dbd/dbd_protocol.spl) and the

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/apps/dbd/dbd_protocol_hardening_spec.spl` |
| Updated | 2026-07-19 |
| Generator | `simple spipe-docgen` (Simple) |

Feeds the db-daemon protocol seam (src/os/apps/dbd/dbd_protocol.spl) and the
RESP wire framing it reuses (std.nogc_sync_mut.redis.server.parse_next_request)
malformed frames, and feeds the journal replay path corrupt/truncated
records. Asserts:

  * malformed RESP frames (wrong/huge length prefix, unterminated, truncated
    bulk) fail closed — parse yields nil or an empty command, never a
    fabricated partial command;
  * a corrupt or truncated journal record is counted but produces an engine
    error and does NOT mutate durable state — the well-formed records around
    it still reconstruct exactly (durability under corruption);
  * oversized keys/values round-trip through the real engine without
    truncation.

Complements the round-trip coverage in dbd_protocol_spec.spl.

## Scenarios

### dbd RESP framing: malformed frames fail closed

#### a truncated bulk (declared len exceeds data) parses as incomplete (nil)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# $5 but only 2 data bytes present -> wait for more, never fabricate
expect(_parse_argc("*1\r\n$5\r\nab\r\n")).to_equal(-1i64)
```

</details>

#### a huge array count with missing elements is incomplete (nil)

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_parse_argc("*999999\r\n$3\r\nfoo\r\n")).to_equal(-1i64)
```

</details>

#### an unterminated array header is incomplete (nil)

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_parse_argc("*3")).to_equal(-1i64)
```

</details>

#### a bulk header with no CRLF is incomplete (nil)

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_parse_argc("*1\r\n$5")).to_equal(-1i64)
```

</details>

#### a non-numeric array count yields an empty command (dispatch -> error)

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_parse_argc("*abc\r\n")).to_equal(0i64)
```

</details>

#### a negative bulk length yields a single empty arg (RESP nil bulk)

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_parse_argc("*1\r\n$-1\r\n")).to_equal(1i64)
```

</details>

### dbd RESP framing: an empty command is rejected by the engine

#### dispatch of empty args returns a RESP error, not a crash

- var eng = DbdEngine new
- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var eng = DbdEngine.new()
val reply = eng.dispatch([])
assert_true(reply.starts_with("-"))
```

</details>

#### dispatch of an unknown command returns a RESP error

- var eng = DbdEngine new
- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var eng = DbdEngine.new()
val reply = eng.dispatch(["BOGUSCMD", "k"])
assert_true(reply.starts_with("-"))
```

</details>

#### a truncated SET (missing value) returns an error and does not store

- var eng = DbdEngine new
- assert true
   - Expected: eng.dispatch(["GET", "k"]) equals `$-1\r\n`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var eng = DbdEngine.new()
val reply = eng.dispatch(["SET", "k"])
assert_true(reply.starts_with("-"))
# key must NOT have been created by the rejected write
expect(eng.dispatch(["GET", "k"])).to_equal("$-1\r\n")
```

</details>

### dbd journal replay: corrupt records do not corrupt the store

#### garbage and truncated records are skipped while valid ones reconstruct

- var eng = DbdEngine new
   - Expected: replayed equals `7i64`
   - Expected: eng.dispatch(["GET", "alpha"]) equals `"$1\r\n9\r\n")   # overwritten`
   - Expected: eng.dispatch(["GET", "beta"]) equals `"$-1\r\n")        # deleted`
   - Expected: eng.dispatch(["GET", "c"]) equals `"$-1\r\n")           # truncated -> never set`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Interleave a truncated SET, an unknown command, and a truncated
# trailing SET among well-formed records.
val journal = "SET alpha 1\nSET\nSET beta 2\nGARBAGE junk\nSET alpha 9\nDEL beta\nSET c"
var eng = DbdEngine.new()
val replayed = eng.replay_journal(journal)
# every non-empty decoded line is attempted (counted)...
expect(replayed).to_equal(7i64)
# ...but only the well-formed mutations changed durable state:
expect(eng.dispatch(["GET", "alpha"])).to_equal("$1\r\n9\r\n")   # overwritten
expect(eng.dispatch(["GET", "beta"])).to_equal("$-1\r\n")        # deleted
expect(eng.dispatch(["GET", "c"])).to_equal("$-1\r\n")           # truncated -> never set
```

</details>

#### a journal of only-corrupt records leaves the store empty

- var eng = DbdEngine new
- eng replay journal
   - Expected: eng.dispatch(["GET", "onlykey"]) equals `$-1\r\n`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val journal = "SET\nDEL\nBOGUS x y\nSET onlykey"
var eng = DbdEngine.new()
eng.replay_journal(journal)
expect(eng.dispatch(["GET", "onlykey"])).to_equal("$-1\r\n")
```

</details>

#### post-corruption writes still succeed (engine not wedged)

- var eng = DbdEngine new
- eng replay journal
   - Expected: eng.dispatch(["SET", "fresh", "ok"]) equals `+OK\r\n`
   - Expected: eng.dispatch(["GET", "fresh"]) equals `$2\r\nok\r\n`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var eng = DbdEngine.new()
eng.replay_journal("GARBAGE\nSET\n")
expect(eng.dispatch(["SET", "fresh", "ok"])).to_equal("+OK\r\n")
expect(eng.dispatch(["GET", "fresh"])).to_equal("$2\r\nok\r\n")
```

</details>

### dbd journal encoding: ambiguous / oversized args

#### an arg containing a space is rejected (returns empty line)

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(dbd_encode_journal_line(["SET", "k", "a b"])).to_equal("")
```

</details>

#### an arg containing a newline is rejected (returns empty line)

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(dbd_encode_journal_line(["SET", "k", "line1\nline2"])).to_equal("")
```

</details>

#### an oversized space-free value round-trips through the engine intact

- var eng = DbdEngine new
   - Expected: eng.dispatch(["SET", "big", bigv]) equals `+OK\r\n`
- assert true
- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bigv = _big(5000)
var eng = DbdEngine.new()
expect(eng.dispatch(["SET", "big", bigv])).to_equal("+OK\r\n")
val reply = eng.dispatch(["GET", "big"])
assert_true(reply.starts_with("$5000\r\n"))
assert_true(reply.ends_with(bigv + "\r\n"))
```

</details>

#### an oversized value survives a journal encode/decode round-trip

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bigv = _big(4096)
val line = dbd_encode_journal_line(["SET", "big", bigv])
val args = dbd_decode_journal_line(line)
expect(args.len()).to_equal(3u64)
expect(args[2]).to_equal(bigv)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 16 |
| Active scenarios | 16 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
