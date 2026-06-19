# BUG: interpreter text/byte primitives unreliable for socket RESP parsing

- **ID:** `interp_bytes_text_roundtrip_search_corruption`
- **Severity:** P2 (blocks pure-Simple wire-protocol servers under `bin/simple run`;
  compiled mode unaffected)
- **Found:** 2026-06-19, while building the pure-Simple Redis (RESP) server
  (`src/lib/nogc_sync_mut/redis/server.spl`).

## Context
A RESP key/value server was implemented and unit-tested. The spec
(`test/01_unit/lib/nogc_sync_mut/redis/server_spec.spl`, 35 assertions) passes
in **both** compiled (`bin/simple test`) and interpreted (`bin/simple run`)
mode. But the live listener (`src/app/redis_server/main.spl`, driven over a real
socket by the existing `RedisClient`) mis-parses RESP **array** commands under
`bin/simple run`, while **inline** commands (`PING\r\n`) parse correctly. Each
of the individual interpreter defects below was isolated to a minimal repro.

## Defect 1 — `rt_text_to_bytes(s)[i]` returns garbage (interp only)
```simple
extern fn rt_text_to_bytes(s: text) -> [u8]
fn main():
    val a = rt_text_to_bytes("AB")
    print(a[0])          # prints 8   (expected 65 = 'A')
```
Indexing the `[u8]` returned by `rt_text_to_bytes` yields pointer/length-strided
i64 fragments, not packed byte values. Note: `"AB".bytes()[0]` returns 80/65
correctly — the defect is specific to the **extern-returned** `[u8]`, not
`text.bytes()`. Compiled mode indexes both correctly (the byte-array version of
the spec passed 34/34 compiled before the text rewrite).

## Defect 2 — `[u8] + [u8]` and `.push`-rebuild corrupt element values
```simple
val c = rt_text_to_bytes("AB") + rt_text_to_bytes("CD")
# c.len()==4 and rt_bytes_to_text(c)=="ABCD" (whole-array convert is fine),
# but c[0]==8 and rebuilding `var d=[]; for i: d.push(c[i])` then
# rt_bytes_to_text(d) yields garbage text.
```
Whole-array `rt_bytes_to_text` is reliable; per-element access / push-rebuild is
not.

## Defect 3 — `.replace` fails in nested-call context
```
semantic: method 'replace' not found on value of type str in nested call context
```
`s.replace("\t", " ").replace("\r", " ")` (or `.replace` used as a sub-expr)
fails on the interpreter. Single-level `.split`/`.trim`/`.substring`/`.char_at`
all work.

## Defect 4 — state-dependent corruption of `index_of`/`starts_with` on `rt_bytes_to_text` output
This is the one that actually breaks the server. On a buffer obtained as
`rt_bytes_to_text(<socket bytes>)`:
```simple
val rt = rt_bytes_to_text(rt_text_to_bytes("*1\r\n$4\r\nPING\r\n"))
val rest = rt.substring(rt.index_of("\r\n") + 2, rt.len())
# rest CONTENT is correct: "$4\r\nPING\r\n"
rest.starts_with("$")      # observed: nil   (not true/false)
rest.index_of("\r\n")      # observed: 0.0   (a FLOAT, not an i64)
```
`index_of` returning a **float** and `starts_with` returning **nil** are memory
corruption, not API contracts. It is **heap-state-dependent**: within one
program a helper that scans `index_of`/`substring` in a loop succeeded three
times on the same value, while the same calls in `main()` returned `0.0`/`nil`.
A clean-state byte dump of the same round-trip showed the bytes perfectly
preserved (`42 49 13 10 36 52` for `*1\r\n$4`), so the round-trip itself is not
deterministically lossy — the search primitives degrade under accumulated heap
state. Same family as the documented `md_slugify_string_corruption`,
`f64 → 0.0`, and tuple-element-corruption interpreter bugs.

## Also observed (already-known family) — `to_int()` typed as bare i64
```simple
val n = "30".to_int()
n.?            # true
n.unwrap()     # semantic: method `unwrap` not found on type `i64` (receiver value: 30)
```
`text.to_int()` is sometimes typed/returned as a bare `i64` rather than
`Option<i64>` on the interpreter, so `.?`/`.unwrap()` crash. Worked around in the
server with a hand-rolled `parse_i64` over `text.bytes()`.

## Impact
- Pure-Simple RESP/line-protocol **servers cannot reliably parse framed input
  under `bin/simple run`** today. The parse/dispatch/store logic is correct
  (proven by the 35-assertion spec in both modes); the failure is purely the
  interpreter byte↔text boundary under load.
- A `redis-benchmark` head-to-head therefore requires a **compiled** server
  binary, not the interpreter. The byte-array spec already passed under
  compilation, indicating the compiled path is sound.

## Repro assets
- `src/lib/nogc_sync_mut/redis/server.spl` — server (parse/dispatch/store/encode)
- `test/01_unit/lib/nogc_sync_mut/redis/server_spec.spl` — 35 passing assertions
- `src/app/redis_server/main.spl` — listener entry (`bin/simple run` it, then a
  raw RESP probe or `RedisClient` shows array commands mis-parsing)
- `test/01_unit/lib/nogc_sync_mut/redis/_smoke_client_driver.spl` — live client
  round-trip driver

## Suggested fix direction (unverified)
Audit the interpreter's `RtCoreString`/`[u8]` boundary: (a) make
`rt_text_to_bytes` return a packed-byte array that indexes element-wise like
`text.bytes()`; (b) ensure `text` values produced by `rt_bytes_to_text` carry a
normalized representation that `index_of`/`starts_with` handle (the float/nil
returns smell like reading a length/ptr field as the result); (c) make
`text.to_int()` consistently `Option<i64>`; (d) allow `.replace` in nested-call
position. Each is independently testable with the minimal repros above.
