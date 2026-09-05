# `rt_engine2d_simd_fill_span_u32` colour-boxing "fix plan" — retracted, no bug found

**Filed:** 2026-08-07 · **Disposition:** §2 of
`doc/08_tracking/bug/engine2d_simd_span_kernels_slower_and_fill_colour_corrupt_2026-08-06.md`
is a **false positive**. This doc was commissioned as a diagnosis + fix plan for
that finding; the diagnosis is that there is nothing to fix. It replaces the
planned Rust-seed code change with the evidence that closes the finding.

## 1. What §2 claimed

> expected `0xFF112233` = `4279173683`; observed `0xFF132233` = `4279312947`;
> the green byte `0x11` comes back as `0x13`, attributed to
> `engine2d_box_pixel`/`engine2d_unbox_pixel` (`runtime_simd_dispatch.c:663`/`:667`).

## 2. Root cause of the *finding*: two hex→decimal conversion errors, not a code bug

Both decimal numbers in that table are wrong. Checked independently (Python and
by-hand, agreeing):

| hex | correct decimal | §2's decimal for it |
|-----|-----------------|----------------------|
| `0xFF112233` | **4279312947** | mislabeled `4279173683` (that number is actually `0xFF0F0233`) |
| `0xFF132233` | **4279444019** | mislabeled `4279312947` (that number is actually `0xFF112233`) |

`4279312947` — the number §2 calls "observed / corrupted" — is the **correct**
decimal value of the **input** colour `0xFF112233`. §2 compared the right
runtime output against a wrong hand-computed expectation and read the mismatch
as corruption. There is no `0x11 -> 0x13` byte change anywhere in the actual
data.

## 3. Live reproduction on current origin/main — confirms no corruption

Ran §2's exact repro against the currently deployed binary
(`bin/release/x86_64-unknown-linux-gnu/simple`, still a Rust-seed build per
`bin/simple --version`'s banner; md5 `c87f00ba282a97592b1d6e6523dce441`,
rebuilt since §2's `ed53cc5f...` but same source):

```simple
use std.nogc_sync_mut.gpu.engine2d.simd_native_rows.{rt_engine2d_simd_fill_span_u32}

fn byte_of(v: i64, shift: i64) -> i64:
    (v >> shift) & 0xFF

fn main():
    var a: [u32] = [0; 8]
    val out = rt_engine2d_simd_fill_span_u32(a, 2, 4, 0xFF112233 as u32)
    var i: i64 = 0
    while i < 8:
        val v = out[i.to_i32()] as i64
        println("out[" + i.to_text() + "]=" + v.to_text() +
                " bytes=" + byte_of(v,24).to_text() + "." + byte_of(v,16).to_text() +
                "." + byte_of(v,8).to_text() + "." + byte_of(v,0).to_text())
        i = i + 1
```

Output:

```
out[0]=0 bytes=0.0.0.0
out[1]=0 bytes=0.0.0.0
out[2]=4279312947 bytes=255.17.34.51
out[3]=4279312947 bytes=255.17.34.51
out[4]=4279312947 bytes=255.17.34.51
out[5]=4279312947 bytes=255.17.34.51
out[6]=0 bytes=0.0.0.0
out[7]=0 bytes=0.0.0.0
```

`255.17.34.51` = `0xFF.0x11.0x22.0x33` — **exactly** the input colour, byte for
byte, in the correct span (`offset=2, count=4` filled indices 2..5, everything
else untouched). This byte-level readout is decimal-independent (uses shift +
mask, not `to_text()` on the whole word), so it is not vulnerable to the same
kind of hand-conversion slip that produced §2's table.

This decisively confirms: **`rt_engine2d_simd_fill_span_u32`'s colour
marshalling is correct.** No further bit-level explanation of a `0x11->0x13`
delta is possible or needed — that delta never occurred.

## 4. Why the box/unbox scheme in `runtime_simd_dispatch.c:663/667` is sound

For completeness (since §2 named these lines as the suspected cause), traced
the boxing math anyway:

```c
static inline int64_t engine2d_box_pixel(uint32_t pixel) {
    return (int64_t)((uint64_t)pixel << 3);
}
static inline uint32_t engine2d_unbox_pixel(int64_t value) {
    return (uint32_t)((uint64_t)value >> 3);
}
```

This is the same `<<3`/`>>3` tag scheme as the general 3-bit-tagged
`RuntimeValue` used everywhere in the Rust runtime
(`src/compiler_rust/runtime/src/value/core.rs`: `from_int` = `(i as u64) << 3`,
`as_int` = `(self.0 as i64) >> 3`, 3-bit tag / 61-bit payload). For a 32-bit
`pixel` value the shift-left-3 fits comfortably inside the 61-bit payload
(max 35 significant bits used), so the round trip `unbox(box(x)) == x` holds
for all `u32` `x` — verified by direct calculation for `0xFF112233` and by the
live probe above, which exercises exactly this code path via
`rt_engine2d_simd_fill_span_u32` -> `rt_engine2d_simd_fill_u32` ->
`engine2d_box_pixel`. No mask, sign-extension, or truncation defect exists in
these two lines.

Also traced the Rust-runtime span implementation with the same C-ABI symbol
name (`src/compiler_rust/runtime/src/value/engine2d_simd_ops.rs:112`,
`#[no_mangle] extern "C" fn rt_engine2d_simd_fill_span_u32`) and the
interpreter-mode Rust glue (`src/compiler_rust/compiler/src/interpreter_extern/simd.rs:1480`)
— both apply the identical `<<3`/`>>3` tag discipline via
`RuntimeValue::from_int`/`as_int` (`collections.rs` `rt_typed_words_u32_push`/
`rt_typed_words_u32_at`) and neither shows a defect either.

**Caveat:** three distinct code paths answer to the symbol
`rt_engine2d_simd_fill_span_u32` (the C runtime, the `#[no_mangle]` Rust
runtime function, and the interpreter-mode Rust glue). This diagnosis
identifies which one `bin/simple run` actually resolves to only by observing
correct end-to-end behavior; it does not independently prove the other two are
bug-free by direct unit exercise. Given all three implement the same box/unbox
math (traced above) and the live probe is correct, this is not treated as an
open risk, but a future session touching any of the three should re-verify
which one is linked before assuming parity.

## 5. §2's *other* claim — performance — is NOT re-examined here

§2 also asserted `fill_span` is *slower* than the marshalling path it would
replace (13 ms vs 8 ms vs <1 ms scalar, same harness as §1). This plan doc did
not re-run `test/perf/graphics_2d/bench_span_kernels.spl` / `run_span_bench.shs`
against current `main`, so that claim is **neither confirmed nor retracted**.
Scope of this retraction is strictly the correctness claim in §2. Do not read
this doc as "fill_span is now adoptable" — the perf question is still open and
should be re-measured (same harness, same tiering) before any adoption
decision.

## 6. §3 (missing in-place blend span kernel) is unaffected

§3's finding — no allocation-free blend path exists, and landing a new
`runtime_simd_dispatch.c` symbol requires a Rust-seed rebuild + redeploy of the
shared `bin/release/x86_64-unknown-linux-gnu/simple` binary, which should be
its own isolated session — still stands. This doc's retraction is scoped to §2
only and does not touch §3's scheduling note.

## 7. Related, and NOT retracted: the sibling `any`-receiver tag bug

`doc/08_tracking/bug/any_receiver_element_read_shift_and_tag_2026-08-06.md` is
a **real, independently-reproducible** defect: `val v: u32 = dst[idx]` (or
`i64`) on an `any`-typed receiver returns the raw tagged word (`value << 3`)
instead of the untagged value, while `dst[idx] as u32` and a typed-array
temporary both read correctly. Verified: `0x11405060` = `289427552`, and
`289427552 << 3` = `2315420416`, matching that doc's reported tagged-word
readback exactly. This defect is exactly the kind of thing that makes a
phantom "colour corruption" easy to manufacture by hand — but it is not what
happened in §2 (§2's repro used `rt_engine2d_simd_fill_span_u32`'s own return
value directly, not an `any`-typed intermediate), and this session's probes
used the safe `as i64` / typed-array read forms throughout, so §2's error is
independently confirmed to be pure arithmetic, not a manifestation of this
sibling bug.

## 8. Action

- **No Rust/C source change is needed.** No fix to schedule, no Rust-seed
  rebuild/redeploy window required for this finding.
- **Amend** `doc/08_tracking/bug/engine2d_simd_span_kernels_slower_and_fill_colour_corrupt_2026-08-06.md`
  §2 to mark it retracted/false-positive, pointing at this doc, in the same
  commit as this doc (done — see that file's new note).
- **Still open, unrelated to this retraction:** §1/§5 perf re-measurement of
  `fill_span` vs the marshalling path, §3's missing blend span kernel (needs
  its own isolated Rust-seed-rebuild session per the board/binary-provenance
  rules in `.claude/rules/bootstrap.md`), and the real `any`-receiver tag bug
  in §7's sibling doc.
