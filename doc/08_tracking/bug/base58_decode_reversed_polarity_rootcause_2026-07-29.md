# base58_decode reversed-polarity engine bug — root cause (2026-07-29)

Status: OPEN (P1)
Status re-verified 2026-08-17 by source inspection (triage shard 00).

Assignment: root-cause the pass-5 finding that `base58_decode`'s
carry-propagation loop corrupted values under the DEFAULT engine while the
interpreter was correct (the reverse of every other engine divergence found
in the bracket-slice campaign). Diagnosis-first; fix only if a contained
base58-side workaround exists.

## Result: TWO distinct, independently-triggered default-engine miscompiles

Both were live in the same function and had to be dodged together. Neither
is a byte/char-index bug (this campaign's usual class) — both are
representation/codegen bugs in how the default engine (JIT/native codegen)
handles the untyped `list` type.

### Bug 1 — empty-list-first-assignment poisons reads after a later rebind

**PROVED**, minimal repro (12-variant shrink from the original function down
to ~6 lines):

```
fn poisoned(digit: i64) -> i64:
    var work = []          # <- first assignment is an EMPTY list literal
    var new_work = []
    new_work.push(digit & 0xFF)
    work = new_work         # <- rebind `work` to a DIFFERENT list object
    val wv: i64 = work[0]   # <- reads back digit<<3 (mod 256), not digit
    wv
```

`poisoned(5)` returns **40** (`5<<3`) under the default engine; **5**
(correct) under `SIMPLE_EXECUTION_MODE=interpret`. `poisoned(57)` returns
**200** (`(57<<3) mod 256`), confirming the shift is applied then the
result is (for `u8`/byte contexts) implicitly masked/wrapped — consistent
with an unboxing (`>>3`) step being skipped for reads through `work`,
i.e. the code path treats already-boxed elements as if they no longer
needed unboxing.

**Discriminating evidence** (each variant isolates one axis; all tested
directly against the default engine, digit=5 unless noted):

| Variant | Shape | Result |
|---|---|---|
| `work=[]` then `work=new_work` (built via `.push`) | rebind to differently-named, freshly-built list | **40 (buggy)** |
| `work=[]` then `work=[digit&0xFF]` (literal) | rebind to a list literal | **40 (buggy)** |
| `work=[]` then `work=other` (`other` pre-built) | rebind to a pre-existing list | **40 (buggy)** |
| Two hops: `work=new_work` then `work=newer_work` | double rebind | **40 (buggy, not 320 — one shift, not compounding)** |
| `new_work.push(...)`, read `new_work[0]` directly, no rebind | never assign into the empty-first var | 5 (correct) |
| `work.push(...)` directly, no second var, no rebind | in-place growth only | 5 (correct) |
| `work = work` (self-rebind) | rebind to itself | 5 (correct) |
| Two separate `var` locals, read the untouched second one | no rebind at all | 5 (correct) |
| Rebind `work = new_work`, but read `new_work` (the source), not `work` | read the un-poisoned name | 5 (correct) |
| `var work = [99]` (**non-empty** first assignment) then `work = new_work` | rebind, but destination didn't start empty | 5 (correct) |
| `var work: list = []` (explicit `: list` annotation) then rebind | annotation doesn't help | **40 (buggy)** |

Conclusion: the trigger is specifically *"a `var`'s first assignment is an
empty list literal, and it is later reassigned (rebound) to a different
list object"* — not rebinding in general, not the type annotation, not the
value being read.

### Bug 2 — loop-carried list growth+index-write across enclosing-loop iterations

**PROVED**, separate minimal repro, found only after Bug 1's fix (which
switched the algorithm to LSB-first accumulation with in-place index writes
+ `.push()`, no rebind) still left multi-digit decodes wrong:

```
fn spilled() -> [i64]:
    val digits = [57, 57]
    var work = []
    var di = 0
    while di < digits.len():          # <- OUTER loop, 2 iterations
        val digit = digits[di]
        var carry: i64 = digit
        var wi: i64 = 0
        while wi < work.len():        # inner: index-read + index-write
            val x = work[wi] * 58 + carry
            work[wi] = x & 0xFF
            carry = x / 256
            wi = wi + 1
        while carry > 0:
            work.push(carry & 0xFF)    # <- growth (reallocation) INSIDE the outer loop
            carry = carry / 256
        di = di + 1
    work
```

Expected `[35, 13]` (hand-traced: first pass produces `work=[57]`; second
pass multiplies by 58 and adds another 57, giving LSB=35, carry-byte=13).
Default engine returns **`[137, 103]`** — not a simple shift this time
(137 isn't `35<<n mod 256` for any small n), consistent with a stale
base-pointer / spill-slot read rather than a value-encoding error.

**Discriminating evidence**:
- The exact same code executed **twice, straight-line** (no outer loop,
  just the block duplicated) → correct `[35, 13]`.
- The exact same code inside a `while di < 2` loop (array-driven or a
  literal counter — both tested) → buggy `[137, 103]`.
- Pre-sizing `work` up front (either via a list literal `[0, 0]` or via a
  separate **pure-push** pre-loop that never interleaves index-reads) so
  the per-digit loop performs **only** in-place index reads/writes and
  never calls `.push()` → correct `[35, 13]` in both cases.

Conclusion: growing a `list` via `.push()` (reallocation) in one iteration
of an enclosing `while` loop, then index-reading/writing that same list in
a *later* iteration of that loop, corrupts the read — a loop-carried
mutable-list spill/clobber. This matches the coordinator-named "native
tuple-spill family" (guide item (d)), but had not previously been isolated
down to this exact minimal shape (push-then-later-index-access across loop
iterations, independent of any rebind).

## Fix (base58-side workaround, both engines proven)

`src/lib/common/encoding/base58.spl`, `base58_decode`:
- Rewrote `work` to be accumulated **LSB-first** (was MSB-first) so growth
  is always an *append*, never a *prepend*, eliminating the need for
  `work = new_work` (Bug 1's trigger) entirely.
- Pre-sized `work` to `indices.len() + 1` bytes via a **separate, pure-push
  pre-loop before the per-digit loop starts** (a shape independently proven
  safe), so the per-digit loop performs only in-place index reads/writes
  and never calls `.push()` (Bug 2's trigger never occurs).
- `n + 1` bytes is a safe upper bound: `n` base58 digits represent a value
  `< 58^n`, needing at most `ceil(n * log2(58)/8) ≈ ceil(n*0.733)` bytes —
  always `< n`, so `n + 1` has comfortable margin regardless of `n`.
- Trims unused high-order (most-significant) pre-allocated zero slots
  before emitting (mathematically safe: `indices[0]` can never be the
  alphabet index for `'1'`, since leading `'1'` characters are already
  stripped into `lz1` before `indices` is built, so the represented value
  is always `> 0` for non-empty `indices`, guaranteeing a nonzero true MSB
  byte — trimming trailing zero high-slots always reproduces the same
  minimal-length result the original algorithm produced).

## Verification (both engines, fixture is a from-scratch python3 reference — never from memory)

10 hand-picked cases (`"1"`, `"z"`, `"11"`, `"1z"`, `"zz"`, `"abc"`,
`"Satoshi"`, and 3 realistic multi-byte-length strings including a real
25-byte Bitcoin P2PKH address body) — reference bytes computed via an
independent from-scratch python3 base58 decoder
(`scratchpad/base58_ref.py`), not this repo's code:

```
1   -> 1  bytes: 00
z   -> 1  bytes: 39
11  -> 2  bytes: 0000
1z  -> 2  bytes: 0039
zz  -> 2  bytes: 0d23
abc -> 3  bytes: 01b97b
Satoshi -> 5  bytes: e2c4bdad81
3P14159ezcVW2p7QASPTC22ff6cJ2fw -> 23 bytes: 01fc750db1594dd943d57400a1559a0d891c01d7445b6e
1BvBMSEYstWetqTFn5Au4m4GFg7xJaNVN2 -> 25 bytes: 0077bff20c60e522dfaa3350c39b030a5d004e839af415766b
111111111111111111114oLvT2 -> 24 bytes: 000000000000000000000000000000000000000094a00911
```

Post-fix: **all 10 cases byte-exact under both the default engine and
`SIMPLE_EXECUTION_MODE=interpret`**, matching the python reference exactly
— the reversed-polarity divergence is gone (fixture decides, per protocol;
both engines now agree with the fixture, so there is no residual
divergence to report for `base58_decode` itself).

**Round-trip** (`base58_encode` → `base58_decode`, encode side already
fixed in pass 4/5) across 12 cases spanning 0–100 bytes, including
leading-zero-byte payloads (`[0]`, `[0,0,0]`, a 3-zero-byte + 20-random-byte
payload) and a `base58check_encode`/`base58check_decode` round-trip: **all
`match=true` under both engines**.

## Vacuity

Before the fix, the same 10-case matrix reproduced the original pass-5
finding exactly: default engine wrong on every case that actually exercises
the carry loop (any input with ≥1 non-`'1'` character), correct only on the
two trivial all-`'1'` cases (`"1"`, `"11"`, which never enter the digit
loop at all) — confirming the bug was real, not a probe artifact, and that
the fix's before/after delta is the genuine signal.

## New, separate, unexamined finding (out of scope this pass)

While round-trip-testing `base58check_encode`/`base58check_decode`, the
same deterministic 20-byte payload produced **different final addresses**
under the two engines (default:
`12J13oCScQMK7FrgunG1W46MUZ3Ff6fpqd`, interpret:
`12J13oCScQMK7FrgunG1W46MUZ3Fg3EGbD`) even though each engine's own
encode→decode round-trip was internally self-consistent
(`payload_match=true` both sides). Isolated the payload-generation helper
itself (`mk_bytes`, an ad hoc probe PRNG) as identical byte-for-byte under
both engines, narrowing the divergence to `_b58_double_sha256_first4` /
`sha256_bytes` (double-SHA256 checksum) — **not investigated further, not
fixed, not related to the carry-propagation bug this pass targeted**.
Flagging for a separate pass/owner (crypto/sha256 lane).

## Campaign status

Closes the base58_decode carry-propagation reversed-polarity bug named as
an open item at the end of the bracket-slice byte/char index campaign
(pass 6 doc). Remaining open items: the kafka `list.get(i)` tag-box bug
(pass 3, stays with the engine investigation lanes) and the newly-found
`sha256_bytes`/base58check-encode engine divergence noted above (new,
unowned).

## Re-verification 2026-08-17 (stdlib slice G, content-classified)

**NOT-REPRODUCED on either engine.** Probe over
`std.common.encoding.base58.{base58_encode, base58_decode}`, run twice — once with
`SIMPLE_EXECUTION_MODE=interpreter` and once on the default JIT (`bin/simple run`),
both rc=0 — produced IDENTICAL output:

```
enc=1LiA
valid_is_err=false
roundtrip=0,1,2,255,
invalid_is_err=true
```

Polarity is correct in both directions (a valid string decodes, the
alphabet-invalid `"0OIl"` errors), the byte round-trip including the leading zero
is exact, and there is no interpreter/JIT divergence — which is what the two
claimed miscompiles would have shown. Note the path in this doc had drifted; the
live module is `src/lib/common/encoding/base58.spl` (`base58_decode` at :212).
Recommend CLOSED, or re-file with a fresh minimal repro if the miscompile is
believed to persist elsewhere.
