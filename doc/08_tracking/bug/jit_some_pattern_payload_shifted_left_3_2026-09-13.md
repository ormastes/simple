# Seed JIT: `Some(x)` payload destructuring returns the value shifted left 3 bits

- **Date:** 2026-09-13
- **Status:** OPEN
- **Severity:** P1 — silent wrong value, no diagnostic, only on the default `run` lane
- **Found by:** July-2026 bug-triage sweep, while re-verifying
  `if_val_some_constructor_pattern_parser_regression_2026-07-02.md`
- **Lane:** seed JIT only. The tree-walk interpreter
  (`SIMPLE_EXECUTION_MODE=interpreter`) is correct.

## Symptom

Destructuring an `Option` payload through the `Some(x)` **constructor pattern**
binds `x` to `payload * 8` (i.e. `payload << 3`) instead of `payload`. Binding
the same Option through the plain `if val x = ...` form is correct, so the two
forms silently disagree.

## Repro (measured 2026-09-13)

```spl
fn get(f: bool) -> i64?:
    if f:
        return 7
    nil

fn main():
    if val Some(a) = get(true):
        print("someptn={a}")
    if val b = get(true):
        print("plainval={b}")
    match get(true):
        case Some(c): print("match={c}")
        case _: print("match=none")
```

Seed JIT lane (`run`, the default):

```
someptn=56
plainval=7
match=56
```

Tree-walk lane (`SIMPLE_EXECUTION_MODE=interpreter run`):

```
someptn=7
plainval=7
match=7
```

`return 5` instead of `return 7` gives `40` on the JIT lane, confirming the
factor is exactly 8 and not a one-off constant.

## Analysis

`56 = 7 << 3` and `40 = 5 << 3`. Three bits is exactly the tag width of the
seed's inline tagged value: `seed_jit_boxed_int_61bit_drops_high_bits_2026-07-22.md`
documents the representation as `(value << 3) | TAG_INT(0)`, unboxed with
`value >> 3`. The `Some(...)` pattern arm therefore appears to bind the
**still-tagged word** — a missing unbox, not a lossy box.

**This is the third site in the same family**, and the second one whose root
cause is a *missing unbox* rather than a lossy box.
`list_get_returns_tag_boxed_value_shifted_left_3_2026-07-28.md` reports the
identical `value << 3` signature for `list.get(i)` on the JIT/native path, and
its 2026-08-09 re-verification states the root cause as "a missing tag-box
decode/unbox step on `.get()`'s call site", explicitly refuting an
address-vs-value explanation. That site is fixed (re-measured 2026-09-13:
`b[0]=42 b.get(0)=42` on both lanes); the `Some(x)` pattern arm is the same
omission at a site that was never swept. Anyone fixing this should check
whether other payload-extraction sites share the gap.

The 61-bit entry is a different defect at a different site, and it is now
closed: re-measured 2026-09-13, the boxed channel itself is 64-bit clean
(`1 << 63`, `1 << 62` and `0x8010000000000000` all round-trip intact through the
array-in-struct boxed path on both lanes). So the general box/unbox pair is
correct and only the constructor-pattern payload extraction is missing its
unbox. Both the `if val Some(x)` form and the `match ... case Some(x)` arm are
affected, so the defect is in the shared constructor-pattern extraction, not in
`if val` specifically.

## A second, non-integer manifestation

The same `case Some(v)` arm also corrupts a payload that did not come from a
literal. Re-running the repro in
`interp_to_int_split_result_nil_coalesce_garbage_2026-07-17.md`:

```spl
val parts = "hello:42:world".split(":")
val n2 = parts[1].to_int()
match n2:
    case nil:   print "n2 is nil"
    case Some(v): print "n2 = {v}"
```

Tree-walk lane prints `n2 = 42`. Seed JIT lane prints `n2 = 0.000…002` — a
float with roughly 300 fractional digits. The surrounding lines (`parts[1]=42`,
and `parts[1].to_int() ?? 0` giving `42`) are correct on both lanes, so it is
again specifically the `Some(v)` arm. Here the tagged word is not merely
shifted but re-typed, which suggests the arm passes the raw word on without
consulting the tag at all rather than applying a wrong-but-uniform shift.

## Impact

Any JIT-lane code that reads an Option payload through `Some(x)` gets a value
8x too large with no error. Because the plain `if val x` form is correct, a
codebase that mixes the two forms is inconsistent rather than uniformly wrong,
which makes this hard to notice.

## Not fixed here

The fix site is in the seed's JIT lowering under `src/compiler_rust/**`. A
bootstrap was running during the triage session that found this, and editing
Rust sources aborts a running bootstrap, so no change was attempted.

## Verification engine

Pinned copy of `src/compiler_rust/target/release/simple.exe`
(Simple Language v1.0.1-beta.1, 39,267,840 bytes, sha256 prefix
`1b62a1a42755774fc087`, built 2026-09-13). Windows 11 / Git Bash.
