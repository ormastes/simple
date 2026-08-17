# Two `list`-parameter stdlib/helper functions return wrong values while byte-identical inline code is correct — one of them silently corrupted a bug investigation

**Date:** 2026-08-08
Status: FIXED
Status re-verified 2026-08-17 by source inspection (triage shard 02).
`doc/08_tracking/bug/jit_param_passed_list_element_read_returns_tagged_2026-08-08.md`

> **Mechanism (was "NOT determined"):** under the JIT, an element read `data[i]`
> from a parameter declared as an untyped `list` yields the value still carrying
> its small-int tag, i.e. `v << 3`. The interpreter is correct. Both reproducers
> here are that one defect. The hex helper's `v / 16` sees `v*8`, giving
> `0810808` where inline gives `010210ff`; `pkcs7_unpad`'s `padding_len` was 16
> instead of 2, so `padding_len > data_len` was true and it early-returned its
> input for VALID padding. Next steps 1-3 below were carried out: step 1 found
> the interpreter/JIT divergence, step 2 bisected it to the `list`-typed
> parameter (a list built *locally inside* the same fn is correct, and a `[i64]`
> parameter is correct), step 3 landed the fail-closed fix plus an
> invalid-padding rejection spec in 6bb978f4a42.
**Severity:** High as a *measurement* hazard. A hex-formatting helper of the
shape everyone writes returned wrong digits with no error, and that wrong
output was written into a landed bug doc and commit message as fact. Also
High for `pkcs7_unpad`, which is a shipped stdlib function that never strips
padding.

## Why this matters more than the two functions

The first reproducer below is a 10-line `list` → hex helper. It produced
plausible-looking hex that was wrong, and it was used to "prove" a root cause
for a different bug. The false numbers were committed (`e51dcaaf8ba`) before
the helper itself was suspected. Any investigation in this tree that formats
bytes through a small helper before comparing them should re-take its
measurements by comparing raw values.

Rule of thumb this establishes: **do not put a helper between the system under
test and the assertion.** Compare raw `list`s with `expect(...).to_equal(...)`.
The AES KAT specs landed in `23839a41331` do exactly that
(`_from_u8` + `to_equal` on raw lists, no formatter), which is why they are
unaffected and remain valid.

## Reproducer 1 — hex-formatting helper returns `v * 8 & 0xFF` per byte

```simple
fn tohex(b: list) -> text:
    val d = "0123456789abcdef"
    var s = ""
    var i = 0
    while i < b.length():
        val v = b[i] & 0xFF
        s = s + d[(v >> 4)..(v >> 4)+1] + d[(v & 15)..(v & 15)+1]
        i = i + 1
    s

fn main():
    println(tohex([0x00, 0x01, 0x02, 0x03, 0x0a, 0x0f, 0x10, 0xd6, 0xff]))
```

```
got  00081018507880b0f8
want 000102030a0f10d6ff
```

Each output byte is the input byte times 8, masked to 8 bits
(1→0x08, 2→0x10, 3→0x18, 0x0a→0x50, 0x0f→0x78, 0x10→0x80, 0xd6→0xb0,
0xff→0xf8). No error, no warning; `raw = {b}` printed alongside shows the
input list is intact.

**Discriminators already run — all of these are CORRECT, so the trigger is
none of them individually:**

- The same slice expression with a literal `v`, with a list-indexed `v`, with
  `v & 0xFF` applied, and with `hi`/`lo` hoisted into their own `val`s — all
  four print `01` correctly.
- The **same loop body written inline inside `main`** over `[0x00, 0x01, 0x0a]`
  prints `00010a` correctly.
- `while i < 16` variants of the same helper, taking `[u8]` and reading via
  `rt_bytes_u8_at`, are correct — this is the form used by the AES KAT probes,
  which produced exact FIPS-197 values.

So: correct inline, wrong when factored into a `fn` taking a `list`.

## Reproducer 2 — `pkcs7_unpad` never strips padding, valid or invalid

`src/lib/common/aes/padding.spl:33`. Reading the source, this should strip 13
bytes of `0x0d` and return `[1,2,3]`:

```
pkcs7_unpad([1,2,3,13,13,13,13,13,13,13,13,13,13,13,13,13])
  got  [1, 2, 3, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13]   (unchanged)
  want [1, 2, 3]
```

It also returns its input unchanged for genuinely invalid padding, for a
zero-length padding byte, and for a padding length exceeding the data — i.e.
it **fails open** as well as failing to function. Every documented early-exit
path returns the input, and so does the success path, so a caller cannot
distinguish "stripped" from "rejected" at all.

A **verbatim local copy** of `pkcs7_unpad` in a single file with no imports
misbehaves identically to the imported one, so this is not an import or
symbol-resolution artifact — but it is also not obviously wrong as source,
which is why source-vs-engine is listed as undetermined.

### Security relevance

`pkcs7_unpad` returning its input on invalid padding is the classic fail-open
padding shape: under a wrong key it would hand raw padding bytes back to a
caller as if they were plaintext. This is exactly why the AES-CBC work in
`23839a41331` did **not** route through it and instead uses local
`_pkcs7_pad_16` / `_pkcs7_unpad_16` inside `modes.spl` that return `nil` on
invalid padding. Those local copies were written for dialect reasons
(`padding.spl` is the old `list`/`.length()`/`.append()` dialect; `modes.spl`
is `[i64]`/`.len()`/`.push()`) and are verified fail-closed by spec; this
finding independently justifies not sharing the implementation until
`padding.spl` is fixed.

`pkcs7_pad` itself is correct — `pkcs7_pad([1,2,3], 16)` returns the right 13
bytes of `0x0d`.

## Possible relationship to the broken AES key schedule

`doc/08_tracking/bug/aes_cipher_spl_block_functions_fail_fips197_c1_2026-08-08.md`
records that `src/lib/common/aes/key_expansion.spl` `expand_key` produces a
correct round key 0 but a wrong round key 1. That is the same directory family
and the same `list`-parameter-plus-indexing shape. Whether the three are one
defect or three is unknown. **Anyone fixing any of them should test this
hypothesis first**, because if it is one engine-level defect then editing the
three sources is a cover-up fix that will not help.

## Deliberately not fixed here

No source edit was attempted on `padding.spl`. Its source reads correct, a
verbatim copy reproduces the failure, and editing code that reads correct to
work around a possible miscompile is a cover-up fix. The mechanism has to be
established first.

## Next steps

1. Determine source-vs-engine: run reproducer 1 under the interpreter, JIT, and
   native paths and compare. A divergence proves engine; identical wrongness
   everywhere points at a shared lowering stage or at the source.
2. Bisect reproducer 1 — it is 10 lines and already known to be correct inline,
   so the delta between inline and `fn`-with-`list`-param is small.
3. Once understood, fix, then add a KAT/round-trip spec for `pkcs7_unpad` that
   feeds it INVALID padding and asserts rejection — the current padding specs
   do not.

## Verified on

Interpreter only, via `bin/simple run`, which on this box is the Rust bootstrap
seed (prints the "bootstrap seed only" banner). JIT, native, and a self-hosted
binary were NOT tried — doing so is step 1 above.
