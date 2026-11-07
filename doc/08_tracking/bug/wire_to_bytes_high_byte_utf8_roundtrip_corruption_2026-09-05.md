# `bytes_to_wire`/`wire_to_bytes` corrupt round trips for byte values >= 0x80
## Open 2026-09-16 — needs owner triage

Reviewed in the 2026-09-16 bug-ledger normalization pass; no resolution
evidence found in the body. This is bookkeeping, not verification.

**Date:** 2026-09-05
**Status:** Open
**Severity:** High — silently corrupts TLS wire lengths/values whenever a byte has its high bit set
**Area:** `src/lib/nogc_async_mut/io/tls_common.spl` (`bytes_to_wire`, `wire_to_bytes`)

## Context

Found while walking the debug ladder (`.claude/skills/lib/debug_ladder.md`) to
verify `doc/08_tracking/bug/wire_to_bytes_returns_empty_2026-07-28.md`. That
older ticket ("wire_to_bytes returns an empty array") is **confirmed FIXED**
by commit `3c302ed3f19a` (2026-08-17) — verified today by running the
original repro table (`"h2"` -> `[104, 50]`, `encode_u8(2)`, `encode_u16_be(9)`)
through `.../target/bootstrap/simple run`; every case now returns the correct
length and real integer elements (`a[0] == 104` compares true, no
"comparing string with integer" error). See the generalization spec written
alongside this doc.

That fix's own test coverage (the bug's repro table, and
`test/01_unit/lib/nogc_async_mut/io/tls_common_wire_guard_spec.spl`) only used
byte values < 128. Probing the same functions over 128-255 — the "adjacent
code path" step of the debug ladder — surfaces a **different, still-open**
defect in the same two functions.

## Symptom

```
wire_to_bytes(bytes_to_wire([127]))        -> [127]        # correct
wire_to_bytes(bytes_to_wire([128]))        -> [128, 0]     # WRONG: len 2, not 1
wire_to_bytes(bytes_to_wire([255]))        -> [255, 0]     # WRONG: len 2, not 1
wire_to_bytes(bytes_to_wire([0,255,128]))  -> [0,255,128,0,0]  # WRONG: len 5, not 3
wire_to_bytes(encode_u24_be(200))          -> [0, 0, 200, 0] # WRONG: len 4, not 3
```

Measured 2026-09-05 with
`/Users/ormastes/simple/src/compiler_rust/target/bootstrap/simple run <probe>`
(interpreter path; no JIT/native lane exercised for this probe). The first
byte value(s) still decode correctly; the corruption is **extra trailing
zero byte(s)** appended past the true length, so `len()` on the result is
inflated whenever any input byte is >= 0x80.

## Root cause (hypothesis, not yet proven at the runtime-source level)

`bytes_to_wire` builds its `text` result by repeated `+`-concatenation of
one-byte strings from `tls_hook_byte_char` -> `rt_byte_char` (a genuine
1-byte C string per `src/runtime/runtime.c:2754`). `wire_to_bytes` then uses
`len(wire)` as its decode loop bound and `wire.char_code_at(i)` per index.
`len()` and `char_code_at()` on Simple `text` are UTF-8-aware (codepoint- or
byte-count, not "always 1:1 with the original raw byte stream"). A raw byte
>= 0x80 is not valid standalone UTF-8, so somewhere in concatenation or
length-counting it is being renormalized/counted as a multi-unit sequence,
inflating `len(wire)` past the true byte count and producing phantom
trailing elements (observed as `0`). This needs runtime-level confirmation
(the `rt_byte_char`/`rt_text_count_codepoints`/text-concat C paths) before a
fix is written — filed here as a data point, not a full root cause.

## Impact

Same call sites named in the original ticket — record-header lengths
(`tls_io.spl:161,166`), Certificate body lengths (`tls_handshake.spl:410,414`),
the pre-master secret (`tls_handshake.spl:206`), Finished ciphertext length
(`tls_handshake.spl:304`) — are all reachable with byte values >= 0x80 in
real TLS traffic (DER-encoded certificate lengths, random values, key
material routinely have the high bit set). Any of those paths that trusts
`len(wire_to_bytes(...))` or iterates the full decoded array gets a wrong,
inflated count and phantom zero bytes appended.

## Repro

`test/01_unit/lib/nogc_async_mut/io/tls_common_wire_to_bytes_high_byte_generalization_spec.spl`
— run via
`/Users/ormastes/simple/src/compiler_rust/target/bootstrap/simple run <spec>`
(no working `simple test` on this host today). **Verdict: RED, 3 of 4
examples fail** (`SPEC FILE VERDICT: ... outcome=ERROR ... passed=1 failed=3`),
matching the symptom table above exactly.

## Unblock condition

Fix `bytes_to_wire`/`wire_to_bytes` to be byte-exact for the full 0-255
range — either route the wire format through a genuinely byte-oriented
buffer type instead of UTF-8-aware `text`, or make `wire_to_bytes` decode by
raw byte position using a byte-count-safe primitive instead of `len()`/
`char_code_at()`. Re-run the generalization spec above; it must go from
`failed=3` to `failed=0` with the SAME assertions (do not weaken them per
`.claude/rules/testing.md`).

## Related

- `doc/08_tracking/bug/wire_to_bytes_returns_empty_2026-07-28.md` (the
  original empty-array defect this generalizes from — that one is fixed).
- `test/01_unit/lib/nogc_async_mut/io/tls_common_wire_to_bytes_repro_spec.spl`
  (reproduction spec for the original, now-fixed defect; GREEN, 4/4).

## 2026-11-07 implementation

The confirmed boundary defect spans both directions. Native `rt_byte_char(0)`
is a NUL-terminated C string and therefore represents an empty string, while
the seed interpreter encoded bytes 128-255 as Unicode scalars. Consequently a
single-character construction cannot own arbitrary wire bytes consistently.

`bytes_to_wire` now validates and collects a complete `[u8]` buffer and crosses
the dedicated counted `rt_tls_wire_from_bytes` ABI once. Unlike public
`rt_bytes_to_text`, the TLS-only carrier does not repair malformed UTF-8;
`wire_to_bytes` uses `text.to_bytes()`,
which returns integer storage bytes rather than Unicode character codes.
`encode_u8`/`encode_u16_be`/`encode_u24_be` route through the same owner.
Coverage now includes all 256 byte values, embedded NUL, and raw sequences that
also form valid UTF-8 (`C2 80` and `E2 82 AC`).

Focused pure-Simple native verification parsed, lowered, and borrow-checked the
standalone all-byte fixture, but the admitted Stage-1 compiler stopped in its
LLVM backend with pre-existing `E-BACKEND-LLVM-CONST-TYPE` diagnostics. The
SPipe spec could not be loaded from the intentionally sparse worktree because
its broader `std.spec`/TLS dependency closure was absent. Release verification
must run the expanded spec with a current admitted full-tree runtime.

An Astra review rejected the first candidate because it used public
`rt_bytes_to_text`, whose native implementations intentionally replace `FF`
with `EF BF BD`. The dedicated ABI above is the correction: interpreter, Rust
runtime, core C, and hosted/native C implementations all construct counted
text from the exact input bytes, while ordinary text conversion remains
unchanged. Runtime unit coverage asserts the complete 0-255 sequence in both
packed and boxed array layouts plus embedded NUL and mixed UTF-8-shaped bytes.

