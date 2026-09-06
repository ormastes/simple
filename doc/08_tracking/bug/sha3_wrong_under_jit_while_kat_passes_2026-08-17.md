# SHA3 returns wrong digests under the JIT while its KAT passes 7/7

- **Filed:** 2026-08-17
- **Severity:** P1 — a cryptographic hash silently returns wrong values on the
  engine that ordinary programs run on, and the test that exists to catch this
  cannot reach that engine
- **Status:** PARTIALLY FIXED 2026-08-17 — the 61-bit wide-int family defect this
  record blamed is now FIXED and proven by ablation (see "2026-08-17 root-cause
  fix" below). SHA3 under the JIT is **still wrong**, for a DIFFERENT, still-open
  reason; that part stays OPEN.

## 2026-08-17 root-cause fix (wide-int family) — FIXED

**Binary identity.** The deployed `bin/simple` is stale for this investigation:

```
$ readlink -f bin/simple && stat -c '%s %y' "$(readlink -f bin/simple)"
/mnt/data/worktrees/simple-main/bin/release/x86_64-unknown-linux-gnu/simple
59537240 2026-08-17 12:58:51.339525019 +0000
```

All numbers below are from a seed built **from current source** in an isolated
target dir (`CARGO_TARGET_DIR=/mnt/data/tmp_target_int61 cargo build --release
--bin simple`), because the deployed binary predates the 2026-08-09 `rt_value_int`
boxing change and therefore reproduces the OLD inline-`<<3` signature instead of
the current one. Pre-fix binary: 59,569,896 bytes, 2026-08-17 14:11. Post-fix
binary: 59,571,360 bytes, 2026-08-17 14:17.

**Probe** (`c3.spl` / `c4.spl`, kept minimal, own file):

```spl
fn shifted(n: i64) -> i64:
    return 1 << n

fn main():
    val v = shifted(60)
    print("var=" + v.to_string())
    var l = [0, 0]
    l[0] = v
    print("arr=" + l[0].to_string())
    val l2 = [shifted(60)]
    print("lit=" + l2[0].to_string())
```

Ablation table, `SIMPLE_EXECUTION_MODE=interpreter` vs `=jit`, same source:

| value | interpreter | JIT, deployed 12:58 seed | JIT, current source (pre-fix) | JIT, after fix |
|---|---|---|---|---|
| `var` (scalar `1<<60`) | 1152921504606846976 | 1152921504606846976 | 1152921504606846976 | 1152921504606846976 |
| `arr` (`l[0] = 1<<60`) | 1152921504606846976 | **-1152921504606846976** | **5981380042337** | 1152921504606846976 |
| `lit` (`[1<<60][0]`) | 1152921504606846976 | **-1152921504606846976** | **5981380042353** | 1152921504606846976 |
| `[1<<62][0]` | 4611686018427387904 | **0** | **5020716653681** | 4611686018427387904 |
| `push(1<<60)` then read | 1152921504606846976 | **-1152921504606846976** | **5020716653697** | 1152921504606846976 |

The three columns are three *different* manifestations of one defect: the old
inline `(v<<3)>>3` 61-bit truncation (deployed seed), then — after `BoxInt` was
routed through `rt_value_int`, which heap-boxes `|v| >= 2^60` as
`HeapObjectType::Int` — the raw **heap pointer** leaking through the unbox
(current source, pre-fix). `5981380042337` is a pointer, not a number.

**Root cause.** `rt_value_unbox_int`
(`src/compiler_rust/runtime/src/value/sffi/value_ops.rs`), which the Cranelift
`UnboxInt` lowering calls, decoded only the UNSIGNED heap box (`as_heap_u64`,
`HeapObjectType::UInt`). A wide SIGNED box (`HeapObjectType::Int`, what
`RuntimeValue::from_int` / `rt_value_int` actually produce for `|v| >= 2^60`) fell
through to the verbatim arm and returned its raw heap pointer. The C twin
(`src/runtime/runtime_native.c::rt_value_unbox_int` -> `rt_core_as_heap_int`)
already handled this correctly — only the Rust seed was missing it.

**Fix** (2 edits, `value_ops.rs` only, no `src/runtime/*.c` touched): decode
`as_heap_i64()` first in `rt_value_unbox_int`, and likewise in `rt_value_raw_i64`
(which otherwise took its `is_heap()` panic arm for a wide signed int).

**Ablation proof of causation:** the "JIT, current source (pre-fix)" column above
IS the fix removed — same source tree, same probe, only the two-hunk edit absent;
the pointer values return.

Wide ints now also survive arithmetic and iteration under the JIT
(`SIMPLE_EXECUTION_MODE={interpreter,jit} .../simple run c5.spl`, identical):
`load=1152921504606846976 shift=16 xor=1152921504606846977 iter=1152921504606846976`.

## Still OPEN: SHA3 under the JIT is wrong for a different reason

With the fix applied, a byte-level probe (no `substring`, to avoid the separate
`text.substring` JIT defect) still diverges:

```sh
SIMPLE_EXECUTION_MODE=interpreter /mnt/data/tmp_target_int61/release/simple run sha3q.spl
SIMPLE_EXECUTION_MODE=jit         /mnt/data/tmp_target_int61/release/simple run sha3q.spl
```

interpreter (NIST, correct): `e256=167,255,198,248,191,30,215,102,...` (a7ffc6f8bf1ed766…);
`abc256=58,152,93,167,...` (3a985da74fe225b2…); `abc512=183,81,133,11,...` (b751850b1a57168a…).

JIT (wrong): `e256=241,26,167,192,18,3,0,0,193,25,167,192,18,3,0,0,...`,
`abc256=161,146,167,192,18,3,0,0,...`. The recurring `…,192,18,3,0,0` is a
little-endian **heap pointer**, so the digest list is carrying heap handles read
as bytes. `ctrl=1<<60` prints correctly in both arms now, so the control no
longer distinguishes the arms — a JIT-vs-interpreter DIFF on the digest itself is
the control from here on. No `[CODEGEN…]` fallback line appeared, so the JIT arm
really compiled.

Ruled out by direct probe (identical in both engines after the fix): wide-int
array store/load/literal/push, `>>`/`&`/`^` on a wide array element, `for`-iteration
sum, list mutated through a `list` parameter and returned from a function.
Remaining lead: `sha3.spl` carries its context as a **tuple** `(list, list, i64,
i64)` with nested lists; a tuple/nested-list element appears to be handed back as
a raw heap handle. That is where to look next.

**Also confirmed, unchanged:** `text.substring` is corrupt under the JIT — a hex
renderer built on it returned repeating 8-character table chunks
(`89abcdef89abcdef…0123456701234567…`) instead of per-byte slices. Deserves its
own record.

Not done here (out of scope of this session, still required by "Required fix shape"):
the subprocess cross-engine spec.

- **Original status:** OPEN, independently CONFIRMED by measurement

## Summary

`SHA3-256` under the **Cranelift JIT** returns digests that do not match the NIST
vectors. The **interpreter is correct**. `sha3_kat_spec.spl` measures
`Results: 7 total, 7 passed, 0 failed` and is **structurally incapable** of
detecting this, because `bin/simple test` runs the tree-walk interpreter while
`bin/simple run` uses the JIT.

A passing crypto KAT is therefore actively misleading here: it certifies the one
engine that was never in doubt.

## Measured evidence

Binary for every number below: `bin/simple` -> `bin/release/x86_64-unknown-linux-gnu/simple`,
the Rust seed, 59,536,728 bytes, mtime 2026-08-16 22:59. Probe kept in its own
minimal file (one unsupported operation silently demotes a whole program to the
interpreter, which would hide the defect). `rc` read on the line AFTER the
command, never through a pipe. Both arms `rc=0`.

| value | `SIMPLE_EXECUTION_MODE=interpreter` | `=jit` |
|---|---|---|
| control `2^60` | `1152921504606846976` | `-1152921504606846976` |
| SHA3-256("") | `a7ffc6f8bf1ed766…` (NIST) | `c0e8cca89df588f3…` |
| SHA3-256("abc") | `3a985da74fe225b2…` (NIST) | wrong |
| SHA3-512("abc") | correct 64 bytes | **first 32 bytes byte-identical to its own wrong SHA3-256("abc")** |

The `2^60` control is load-bearing: it diverges, which proves the JIT arm
actually ran rather than being silently demoted to the interpreter.

The SHA3-512/SHA3-256 prefix identity is the strongest single clue — a numeric
slip does not make one function's output a prefix of another's. It points at a
shared corrupted buffer or a mis-sized read, not at the sponge arithmetic.

## Probable family, not a `sha3.spl` defect

The `2^60` control diverging in the same run puts this with the **61-bit
boxed-int truncation** family: the inline form is `v<<3` plus a 3-bit tag, so any
`|v| >= 2^60` loses its top bits. That family already spans roughly ten filed
docs. Do NOT patch `sha3.spl` before testing the family hypothesis — a local fix
there would mask the shared cause and leave every other consumer wrong.

## Related new finding, same session

**`text.substring` is also corrupt under the JIT** — a hex renderer built on it
returned whole 8-character table chunks instead of per-byte slices. This is not
on the previously published list of divergent builtins and deserves its own row.

## Why the test suite cannot catch this class

`test` is the tree-walk interpreter; `run` is the Cranelift JIT. 711 of 23,958
spec files call at least one method that is known to diverge between the two, and
they would all stay green through any JIT regression. See
`doc/08_tracking/bug/run_vs_test_harness_divergence_2026-07-28.md`.

For anything cryptographic this is not a theoretical gap: the KAT is the control,
and the control is blind on the engine that matters.

## Reproduce

Write a minimal `.spl` printing the digest bytes, then run it twice and diff:

```sh
SIMPLE_EXECUTION_MODE=interpreter bin/simple run probe.spl > a.out
rc=$?
SIMPLE_EXECUTION_MODE=jit bin/simple run probe.spl > b.out
rc=$?
diff a.out b.out
```

Keep the probe minimal and in its own file. Include a `2^60` value as a control so
a silent demotion to the interpreter cannot read as "no bug".

## Required fix shape

1. Establish whether the 61-bit truncation family explains it. If so, fix the
   family, not `sha3.spl`.
2. Ship a **subprocess cross-engine** spec — a spec body alone runs interpreted
   and can never go red on this. Copy the pattern in
   `test/01_unit/compiler/codegen/scalar_slot_roundtrip_class_spec.spl`.
3. Prove causation by ablation: apply, verify, then REMOVE the fix and confirm
   the wrong digests return.

## 2026-08-17 20:1x — re-run on the DEPLOYED seed: wide-int half CONFIRMED, SHA3 half STILL OPEN

Binary: /mnt/data/worktrees/simple-main/bin/release/x86_64-unknown-linux-gnu/simple (bin/simple), md5 669150b61f2f20401a6a895ae54e9fee, 59550432 bytes, mtime 2026-08-17 20:10:45 — the REDEPLOYED seed carrying this session's fixes.

Wide-int probe (`c3b.spl`, scalar / array-store / array-literal / 1<<62 / push),
interpreter vs jit on the deployed binary — **all five identical, all correct**:

```
var=1152921504606846976  arr=1152921504606846976  lit=1152921504606846976
lit62=4611686018427387904  push=1152921504606846976      (both engines)
```

SHA3 cross-engine probe (`sha3p.spl`) still DIVERGES on the deployed binary:

```
$ SIMPLE_EXECUTION_MODE=interpreter bin/simple run sha3p.spl > a.out   (rc 0)
$ SIMPLE_EXECUTION_MODE=jit         bin/simple run sha3p.spl > b.out   (rc 0)
$ diff a.out b.out
< e256=a7ffc6f8bf1ed76651c14756a061d662f580ff4de43b49fa82d80a4b80f8434a   (correct KAT)
> e256=89abcdef89abcdef0123456701234567...   (JIT: wrong, and wrong LENGTH)
```

`ctrl=1152921504606846976` in both, so this is not a silent demotion and not the
61-bit family. Confirms this row's own "Still OPEN: SHA3 under the JIT is wrong for
a different reason" section: the JIT digest is not merely wrong bytes but the wrong
length, and repeats `89abcdef`/`01234567` — Keccak state words leaking rather than a
truncation. No regression vs the isolated build (which also only closed the wide-int half).

**Status: wide-int family RESOLVED on the deployed seed; SHA3-under-JIT STILL OPEN.**
