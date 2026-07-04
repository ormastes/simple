# Bug: HPACK huffman single-symbol decode returns empty; concat-built [u8] encodes wrong

**Date:** 2026-06-30
**Severity:** Medium — `hpack_huffman_decode` drops short payloads; blocks
`hpack/huffman_h2_spec` "round-trips 256-byte indexed payload".
**Component:** `src/lib/common/hpack/huffman_h2.spl` and/or interpreter array
handling (`out.push` in nested loop, `[u8]` concatenation).

## Symptoms (via `bin/simple run`)

1. `hpack_huffman_encode([97])` → `[0x1F]` (correct: 'a' = 00011, 5 bits, + 111
   pad). But `hpack_huffman_decode([0x1F], 0, 1)` → `Ok([])` — **empty**, the
   symbol is dropped. Expected `[97]`.
2. Building the payload by concatenation changes the ENCODE length:
   `val p:[u8]=[97]` → enc len 1 (correct); but `var p:[u8]=[]; p = p + [97]`
   → enc len **4**. The concat-built array does not encode as `[97]`.
3. The spec's `_make_indexed(256)` (loop-built) round-trip fails; the 100-byte
   *repeating* payload passes (different construction / lands on a byte boundary).

## Analysis

The huffman tables, encode bit-packing, decode tree build (`_build_decode_tree`),
and tree accessors (`_tree_child`/`_tree_symbol`) all read correctly on
inspection. Yet a correctly-encoded single symbol decodes to empty with
`is_ok=true` and no error — meaning either the leaf match (`_tree_symbol`) never
returns Ok for it, or `out.push(sym)` does not persist. Combined with the
concat-built-array encode anomaly (#2), the likely root is **interpreter array
semantics** (push inside nested `while` loops, and/or `[u8]` concatenation
producing a corrupted array), not a huffman-algorithm error. Same family as
`interp_crossmodule_array_writeback_lost_in_bdd_closure` and the documented
"array-arg mutation lost" / "array .get(>=1) corruption" interpreter issues.

## Repro

```simple
use std.common.hpack.huffman_h2.{hpack_huffman_encode, hpack_huffman_decode}
fn main():
    val enc = hpack_huffman_encode([97])         # [0x1F], len 1 — correct
    val res = hpack_huffman_decode(enc, 0, enc.len())
    print(res.unwrap().len().to_text())          # prints 0, expected 1
```

## ROOT CAUSE FOUND: `[u8]` concatenation corrupts elements (`v << 3`)

Minimal repro (pure `bin/simple run`, `fn main`, NO BDD):
```simple
var p: [u8] = []
p = p + [97]
print(p[0].to_i64().to_text())   # prints 8, expected 97
```
Confirmed pattern for `[u8] [] + [v]` → `(v << 3) & 0xFF`:
`0→0, 1→8, 8→64, 97→8, 200→64, 255→248` (all = `v*8 mod 256`). Multi-element and
non-empty-base cases show cumulative bit-misalignment (`[]+[97,98]→8,3`;
`[10]+[97]→[..,0]`), i.e. a packed-bitstream concat mis-aligning ~3 bits/element.
`[i64] [] + [97]` → 97 (correct). So the bug is **`[u8]`-specific array `+`
concatenation** in the seed interpreter; `.push()` is correct (`q.push(97)`→97).

This is the real root: HPACK huffman (and any `[u8]`-building code using `+`)
corrupts. The huffman encode/decode algorithm is fine; the test/library build
`[u8]` via `+`. **Seed fix** (Rust interpreter, needs rebuild): find the `[u8]`
value representation + its `+`/concat path (likely a packed `Vec<u8>` whose
concat bit-packs instead of element-copies), make it copy elements like the
generic `Value::Array` extend at `interpreter/expr/ops.rs:649-652`. WORKAROUND in
pure-Simple: use `.push()` per element instead of `arr + [x]` for `[u8]`.

## Localization (precise)

Triggered by **reassignment to a `[u8]`-typed variable**, not by the concat or
declaration:
- `var a: [u8] = [97]; a[0]` → 97 (literal decl OK)
- `var e = []; e = e + [97]; e[0]` → 97 (untyped var OK)
- `var d: [u8] = []; d = d + [97]; d[0]` → 8 (typed-var REASSIGN corrupts)
- `var f:[u8]=[10]; var g:[u8]=[97]; (f+g)[1]` → 0 (right-operand elem corrupts)

So an array-element coercion keyed on the variable's declared `[u8]` type runs on
reassignment and mis-packs. The scalar `let`-coercion at
`interpreter/node_exec.rs:118-147` only matches `Type::Simple("u8")` (not the
array type `[u8]`), and the generic `Array+Array` extend at
`interpreter/expr/ops.rs:649-652` just clones — so the buggy coercion is a
separate array-by-declared-type path on the assignment statement (not the let).
Find it by grepping the assignment/store path for where a `[u8]`/list-of-u8
declared type re-coerces RHS array elements. WORKAROUND (pure-Simple): build
`[u8]` with `.push()`, never `arr + [x]`, OR bind the concat to an UNTYPED `var`.

## KEY SIGNATURE: `[u8]+[u8]` bit-concatenates (not element-copy)

Decisive experiment (typed `[u8]`, `bin/simple run`, `fn main`):
- `[10,97,200]` literal → 10,97,200 OK; `[10]` then `.push(97)` → 10,97 OK.
- `var c:[u8]=[10]; var d:[u8]=[97]; var e=c+d` → e = **10,0** (LEFT elem
  preserved, RIGHT elem corrupted).
- `var f=[10]; var g=[97]; f+g` (UNTYPED) → 10,97 OK.

Corruption rule: the **right operand's** element is shifted by the **left
operand's bit-length**, then byte-masked:
- empty left → `97 << 3 & 0xFF` = 8 (and `1→8, 8→64, 255→248`).
- `[10]` left (10 = 4 sig bits) → `97` lands mis-aligned → 0.
So `[u8] + [u8]` is performing a **BIT-LEVEL concatenation** of the two operands
(treating them as packed bitstreams) instead of an element-wise array append.
The left operand survives because it occupies the low bits; the right operand is
shifted into high bits and lost on the byte mask. This is NOT the
`Value::Array + Value::Array` path (that element-copies, verified) — `[u8]` must
have a packed-byte/bitstream representation with its own `+` operator, OR a
type-directed Add that bit-packs when both operands are u8-width. **The fix is to
make that path element-append like `Value::Array`.** Find it by grepping the Add
/ binop dispatch for u8/uint-width handling that builds a result from bit-shifts
(`<<`, `_pow2`, width-based packing) on array operands.

## Seed paths RULED OUT by static reading (start here)

Read and cleared — the `×8` is NOT in any of these:
- `interpreter/node_exec.rs:1370 try_array_append_in_place` (the `arr = arr + [x]`
  fast path) — pushes the evaluated RHS value uncoerced; no element transform.
- `interpreter/expr/ops.rs:649-652` `(Array, Array)` Add — `extend(b.iter().cloned())`,
  pure clone, no coercion.
- `interpreter/node_exec.rs:118-147` let-coercion — only matches scalar
  `Type::Simple("u8")`, not the array type `[u8]`.
- `Value` has no packed-byte variant; `[u8]` is `Array(Vec<UInt{width:8}>)`.

Contradiction: typed `var d:[u8]=[]; d=d+[97]` → 8, but untyped `var e=[]` →
97, through the SAME fast path. So either the typed empty `[u8]` is stored as a
NON-`Value::Array` variant (making the fast path skip → slow path corrupts), or
there is a typed-array concat/literal path not yet located. **Next:** add
`eprintln!` in `exec_assignment` (node_exec.rs:531) to print the `Value` variant
of `d` before/after `d = d + [97]`, rebuild seed, observe — that pins it in one
cycle. (Deferred here: needs instrumented rebuild iterations.)

## Next step (deferred — deep)

Isolate whether `out.push` in the decode's nested loop loses elements, or `[u8]`
concat corrupts, with a minimal non-huffman repro; fix in the interpreter (seed)
or rework the huffman loops to avoid the offending array pattern (e.g. index
assignment into a pre-sized array instead of push/concat). Multi-hour; same
class as the other interpreter array bugs.
