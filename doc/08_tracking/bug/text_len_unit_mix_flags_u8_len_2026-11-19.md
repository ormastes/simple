# text-len-unit-mix gate flags `.len()` on `[u8]` fields

Date: 2026-11-19. Status: open. Gate: `scripts/check/check-text-len-unit-mix.shs` (awk `scan_file`).

## Shape (false positive)

The gate exempts `.len()` only on a simple receiver that is an explicit `[u8]` parameter or
`val/var x: [u8]` local (`byte_receiver()`, per-function binding stack). It deliberately returns
"not bytes" when the receiver is preceded by `.` (so `object.bytes.len()` is not confused with a
parameter named `bytes`). A `[u8]` struct FIELD or element-of-field access therefore has no type
the awk scanner can see, and Rule 2 (`sameline`: X.len() on the same line as a `byte_len()`
receiver) reports it as "(len() as byte width)":

```
for count in [measurement_wire.byte_len(), bytes.stdout.len(), bytes.stderr.len()]:
size in [output.path.byte_len(), output.content.len()]
```

Here `stdout`, `stderr`, `output.content` are `[u8]`, so `.len()` is already a byte count and
the mix is not a unit error. The receiver name extracted is the last path segment (`stdout`),
with no type information.

## Workaround site (PR #10349)

`remote_container_byte_count_v3(data: [u8]) -> i64` at
`src/app/buildrunner/remote_container_evidence_v3.spl:42`, called from
`remote_container_bundle_codec_v3.spl:34` and `remote_container_evidence_v3.spl:110-111`. It exists
only so the argument becomes an explicit `[u8]` parameter the gate can see.

## Why not a cheap gate fix

Field types need struct declarations, often in another file; matching by field name alone
collides (`content`, `stdout` are `text` in other structs) and would silently exempt real
text-vs-byte mixes. A safe fix needs a two-pass scan: collect `struct` field annotations
`name: [u8]` across the scanned roots keyed by (struct, field), and resolve receiver
`a.b.len()` through a typed binding of `a`. That requires local type inference the awk gate does
not have.

## Fix

1. Preferred: port the gate to the pure-Simple lint (`src/compiler/90.tools/lint/`) where field
   types resolve, flag only when the receiver's resolved type is `text`.
2. Interim shell option: two-pass field map keyed by struct+field with parameter/local typed
   receivers only; selftest fixtures: `[u8]` field `.len()` beside `byte_len()` must PASS, a
   `text` field `.len()` beside `byte_len()` must still FAIL.
3. Follow-up (blocked on the container lane finishing its edits to `src/app/buildrunner`): once
   the gate resolves `[u8]` fields, delete `remote_container_byte_count_v3` and its export and
   use `.len()` directly at the three call sites.
