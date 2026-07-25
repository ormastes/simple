# seed JIT: `me`-method write-back into a `self` array-of-structs field crashes ("nil receiver")

**Status:** OPEN (seed JIT/native only; interpreter correct). Workaround in place.
**Found:** 2026-07-23, building `src/lib/hardware/link_mux/mux.spl`.
**Severity:** medium — silently crashes (SIGILL, exit 132) any program that uses
the natural stateful-object idiom below under the default JIT; interpreter is
fine, so it hides until a JIT run.

## Symptom

`runtime error: field access on nil receiver` then abort (exit 132), under the
default JIT. The same program prints the correct result under
`SIMPLE_EXECUTION_MODE=interpreter`. Because the abort discards buffered stdout,
prints *before* the crash appear to never run — misleading during bisection.

## Trigger

A `me` method that reads an element out of a `self` field that is an
**array-of-structs where the element struct has an array field**, mutates the
element's array, and writes the element back — called for **two different
indices** — followed by a *second* `me` method that also writes back elements of
the same `self` array. One writeback method alone, or doing the identical
mutation inline in a free function / `main` (mutating a **local** array instead
of `self.field`), does **not** crash.

## Minimal repro (crashes under JIT, prints `N DONE` under interpreter)

```simple
struct S:
    data: [u8]
    head: i64
struct Holder:
    bufs: [S]
    num: i64
    rr: i64
impl Holder:
    me push(ch: i64, d: [u8]):
        var cb = self.bufs[ch]
        var i = 0
        while i < d.len():
            cb.data.push(d[i])
            i = i + 1
        self.bufs[ch] = cb
    fn pending() -> bool:
        var i = 0
        while i < self.num:
            if self.bufs[i].data.len() > self.bufs[i].head:
                return true
            i = i + 1
        false
    me pump() -> i64:
        var ch = self.rr
        var tries = 0
        while tries < self.num:
            var cb = self.bufs[ch]
            if (cb.data.len() - cb.head) > 0:
                cb.head = cb.data.len()
                self.bufs[ch] = cb
                self.rr = (ch + 1) % self.num
                return ch
            ch = (ch + 1) % self.num
            tries = tries + 1
        0 - 1
fn main() -> i64:
    var arr: [S] = []
    var i = 0
    while i < 4:
        var e: [u8] = []
        arr.push(S(data: e, head: 0))
        i = i + 1
    var h = Holder(bufs: arr, num: 4, rr: 0)
    var d0: [u8] = []
    d0.push(0x41.to_u8())
    var d2: [u8] = []
    d2.push(0x42.to_u8())
    h.push(0, d0)          # write-back bufs[0]
    h.push(2, d2)          # write-back bufs[2]  (different index)
    var n = 0
    while h.pending() and n < 50:
        val c = h.pump()   # second me-method writing back bufs[ch]
        n = n + 1
    print("N DONE pumps={n}")
    0
```

## What does NOT crash (isolation results)

- Same array-of-structs writeback for two indices done **inline in `main`** (local
  array, not `self.field`) — OK.
- A **single** `me` writeback method for two indices, followed by a read-only
  method — OK (`total()` variant).
- `me` writeback to the **same** index repeatedly (single-channel drain, 63
  iterations) — OK.
- Free-function style: `fn h_push(h, ch, d) -> Holder` that copies `h.bufs` into
  a **local** `var bufs`, mutates `bufs[ch]`, and returns `Holder(bufs: bufs,…)`
  — OK. **This is the workaround.**

So the fault is specific to JIT codegen for `self.<array-of-structs>[i] = cb`
write-back inside a `me` method, when it happens across ≥2 methods / indices.
Likely an aliasing/uniqueness or store-lowering defect on the `self`-field array
path (mutating a `self` array-of-structs element aliases/nils a slot).

## Workaround (applied)

`src/lib/hardware/link_mux/mux.spl` uses **functional free functions** (mutate a
local array, return a new struct) instead of `me` self-mutation — matching the
`src/lib/hardware/soc_rtl/*` idiom (`uart_mmio_write(u,…) -> u`). Confirmed to run
correctly under JIT. Remove the workaround note here if/when the seed is fixed.

## Fix direction (seed, Rust)

Inspect the cranelift/native lowering of struct-field array element store where
the element is itself a heap struct with an array field, inside a method whose
receiver is passed by reference — the `self` array slot appears to be nil'd
(freed/moved) after the first cross-index write-back. Compare against the
free-function path which is correct. Related landmines:
`.claude/rules/language.md` (arrays are value types) and the boxed-int JIT class
in `seed_jit_boxed_int_61bit_drops_high_bits_2026-07-22.md`.
