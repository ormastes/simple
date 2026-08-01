# `list.get(i)` returns the raw tag-boxed word (`value << 3`) on the JIT/native path

- **Filed:** 2026-07-28
- **Severity:** P0 — silent wrong values, no error, on the DEFAULT engine
- **Status:** OPEN
- **Affects:** every `list.get(i)` call site returning an integer. Index read `a[i]` is CORRECT.

## Symptom

`xs.get(i)` returns the value multiplied by 8 — the untagged/unshifted box word —
while `xs[i]` on the same element returns the correct value. There is no warning,
no error, and no fallback log. The program simply computes wrong numbers.

```simple
fn main():
    var a = [5, 7]
    print "a[0]={a[0]} a.get(0)={a.get(0)}"       # a[0]=5 a.get(0)=40
    a[1] = 9
    print "a[1]={a[1]} a.get(1)={a.get(1)}"       # a[1]=9 a.get(1)=72
    var b = []
    b.push(42)
    print "b[0]={b[0]} b.get(0)={b.get(0)}"       # b[0]=42 b.get(0)=336
```

Not scoped to a receiver kind or a call site: a local in `main`, a local in a
normal `fn`, and a `list` parameter all reproduce identically. Literal lists,
stored-into lists, and pushed-into lists all reproduce. The factor is exactly 8
(`<< 3`), the tag-box shift.

## Which engine

Byte-identical source, same binary:

| engine | `a.get(0)` on `[5]` |
|---|---|
| JIT / native (default) | **40** — WRONG |
| tree-walk interpreter | 5 — correct |

The interpreter row was obtained by forcing a fallback (adding a function that
trips W1006 `mutation without mut capability`, which demotes the whole program).
**`SIMPLE_NO_JIT=1` does NOT reach the interpreter** — see the companion defect
below; with that env var set the same file still prints 40.

## Companion defect: engine selection was fail-open — RESOLVED `b7151d94114`

`SIMPLE_NO_JIT=1` never selected an engine; it only moved the interpreter's
internal JIT threshold, and the Rust seed has no reader for it at all. So
`SIMPLE_NO_JIT=1 bin/simple run` prints the JIT's `40`. Likewise `--interpret`
/ `--no-jit` were discarded and `bin/simple-interp` set nothing.

**The knob that works is `SIMPLE_EXECUTION_MODE=interpret`.** An unrecognized
value silently falls through to JIT (`exec_core.rs:41 _ => ExecutionMode::Jit`),
so a typo reads as a successful interpreter run. Verified truth table:

| invocation | `a.get(0)` on `[5]` |
|---|---|
| default | 40 (JIT) |
| `SIMPLE_EXECUTION_MODE=interpret` | 5 (interpreter) |
| `SIMPLE_EXECUTION_MODE=interpreter` | 5 |
| `SIMPLE_EXECUTION_MODE=typo_xyz` | 40 — fails open |
| `SIMPLE_NO_JIT=1` | 40 — no-op on the seed |

Fixed in `b7151d94114` (synonym accepted, `SIMPLE_NO_JIT`/`--no-jit` mapped to
force-interpret, unrecognized values warn, wrapper exports the variable); the
seed keeps ignoring `SIMPLE_NO_JIT` until the next bootstrap. Guide:
`doc/07_guide/runtime/execution_engine_selection.md`. **Any past "reproduced
under both engines" claim resting on `SIMPLE_NO_JIT` proved nothing.**

## Blast radius

5,116 `.get(` call sites across 696 owned `.spl` files (excluding vendored trees).
Not all are list receivers — `Dict.get` is a separate, separately-broken API — but
the integer-list users are the dangerous ones. Concentrations, all byte-array code:

- `src/os/crypto/sm3.spl` (54), `src/lib/common/crypto/sha256_simd.spl` (49),
  `src/lib/common/crypto/sha1.spl` (44), `src/lib/common/jwt/sign.spl` (43)
- `src/os/crypto/bip39.spl` — `_set_bit` reads `old_byte = bytes.get(byte_idx)`

### BIP-39 concrete impact

`_set_bit` is currently *accidentally* correct: `src/os/crypto/bip39.spl:87`
mutates without a `mut` capability, which trips W1006 and demotes the entire
program to the interpreter, where `.get()` is right. Remove that demotion — for
example by "fixing" the warning with a `mut` annotation — and entropy→mnemonic
encoding silently corrupts on the second bit set into any byte:

    old_byte = get(0) = 128 << 3 = 1024;  1024 | 64 = 1088  (expect 192)

That is unrecoverable-wallet territory. **Do not add `mut` to any
`src/os/crypto/**` function until this is fixed.** The demotion is the safe state.
91 functions in `src/os/crypto` alone have the same W1006 shape (ChaCha20
`_quarter_round`, `poly1305_init`, `p256._sc_be_store_u64`, `curve448._x448_store28`,
`camellia._wr64`, `paseto._p4_qr`, …).

## Root cause (to confirm)

`list.get` returns the boxed slot word without applying the unbox shift that the
index-read path (`a[i]`) applies. Fix belongs in the compiler / runtime lowering
of the `get` method on list, NOT in a sweep of 5,116 call sites.

## Not the cause

The `mut` parameter annotation is innocent. A first investigation concluded
"adding `mut` corrupts output ×8"; that was a probe artifact — the probe read
results back through `.get()`. With the store verified through `a[i]`, the
`mut` and non-`mut` stores are both correct (1/3/16/100 stored, 1/3/16/100 read).

## Repro files

`~/.claude/jobs/4403a7d8/tmp/{getbug,scope,scope_demoted,min_cmp}.spl`

## Related

- `doc/07_guide/language/dict_native_pitfalls.md` — `Dict.get()`/`Dict.len()` are
  separately broken under native codegen. The two defects are independent; both
  make `.get()` unsafe.
