# `rt_string_to_int` silently truncates its input at 63 bytes — returns a WRONG NUMBER, no diagnostic

- **Filed:** 2026-08-31
- **Severity:** HIGH — silent wrong-answer on a core-required numeric parse; `rt_string_to_int_lenient` aliases it and truncates identically
- **Status:** RESOLVED 2026-08-31 — patch applied and behaviorally verified on Windows/MinGW (see "Resolution evidence")
- **Found by:** `doc/08_tracking/test/rt_test_coverage_audit_2026-08-31.md` §7 R2 (`rt_core_abi_untested_selfcheck.c`)

## Symptom

`src/runtime/runtime_native.c` (`rt_string_to_int`, at :5391 in the Windows
MAIN checkout where the fix landed; line numbers drift per checkout):

```c
int64_t rt_string_to_int(int64_t value) {
    RtCoreString* s = rt_core_as_string(value);
    if (!s) return 0;
    char buf[64];
    uint64_t n = s->len < sizeof(buf) - 1 ? s->len : sizeof(buf) - 1;
    if (n > 0) memcpy(buf, s->data, (size_t)n);
    buf[n] = '\0';
    return (int64_t)strtoll(buf, NULL, 10);
}
```

Any input longer than 63 bytes is parsed as its first 63 bytes. Measured (by
the audit's selfcheck, executed): the 64-character string `"0"*62 + "42"` —
whose numeric value is 42 and fits `i64` comfortably — returns **4**. Not an
error, not a clamp: a plausible-looking wrong number. Long inputs with leading
zeros, leading whitespace, or genuinely long digit runs are the realistic
triggers. `rt_string_to_int_lenient` (`runtime_native.c:5380`) is a direct
alias, so the canonical `int(text)` lowering truncates identically.

## What the other lanes do (divergence matrix)

| lane | limit | overflow behavior |
|---|---|---|
| C native `rt_string_to_int` (`runtime_native.c:5344`) | **63 bytes, silent** | strtoll clamp to INT64_MAX/MIN |
| Rust crate `rt_string_to_int` (`collections.rs:4187`) | none (`str::parse`, strict whole-string) | 0 on any failure |
| Rust crate `rt_string_to_int_lenient` (`collections.rs:4218`) | **none** | `saturating_mul/add` clamp |
| simple_core `rt_string_to_int` (`core_string.spl:1045`) | **none** (`_sffi_core_string_strtoll` in place) | strtoll clamp |

So the C native lane is the only one with a length cliff. This is a
C-vs-everyone silent divergence on a core-required symbol.

## Fix choice, with justification

Three candidates were weighed:

1. **Larger fixed buffer** — moves the cliff, keeps the defect class. Rejected.
2. **Explicit error** — changes the long-documented total, non-erroring
   contract (the function's own comment block and the Rust lenient docs both
   specify "never fails, 0 only when no digits"), and diverges from every
   other lane. Rejected.
3. **Heap fallback (chosen):** stack `char[64]` for the common short case,
   `malloc(len+1)` + copy + NUL + `strtoll` + `free` beyond it; `malloc`
   failure returns 0, mirroring the existing `!s -> 0` arm. This removes the
   cap while preserving strtoll's exact lenient semantics (whitespace/sign
   skip, longest digit prefix, INT64 clamp) byte-for-byte for all lengths.

**Lane matched:** the uncapped lenient parse — Rust
`rt_string_to_int_lenient` and `simple_core/core_string.spl` — which is the
most defensible behavior: total, no length cliff, saturating on overflow
(strtoll's INT64_MAX/MIN clamp is the C analogue of Rust's saturating
arithmetic). Current behavior (silent truncation of a numeric parse) is the
worst of all options and matches nothing.

A copy is still required in the general case because `strtoll` needs a
NUL-terminated buffer; `RtCoreString` allocation (`rt_string_new_uncached_impl`,
`runtime_native.c:2591`) does write `s->data[len] = '\0'`, but the fix does
not bet on every producer of an `RtCoreString*` upholding that invariant.

## Unix impact

Pure C stdlib (`malloc`/`free`/`strtoll`/`memcpy`, `SIZE_MAX` from
`stdint.h`/`limits.h` already included by the TU). No platform conditionals.
Linux/macOS get the identical semantic fix; no behavior change for inputs
under 64 bytes (same stack path, same strtoll call).

## Test note

The audit's `src/runtime/test/rt_core_abi_untested_selfcheck.c` pins this
defect RED; per `.claude/rules/testing.md` it stays RED until this patch
lands, then goes green unmodified.

## Resolution evidence (measured 2026-08-31, Windows/MinGW gcc 15.2.0)

`runtime_native.c` compiled unmodified from the tree, linked into a harness
(unrelated symbols stubbed), executed before and after the patch:

| input (64 bytes) | BEFORE | AFTER |
|---|---|---|
| `"0"*62 + "42"` | **4** | **42** |
| `"0"*55 + "123456789"` | **12345678** (last digit dropped) | **123456789** |

`src/runtime/test/rt_core_abi_untested_selfcheck.c` I0-I7, unmodified:
BEFORE `FAIL I5 (got 4, want 42)`; AFTER all PASS (23/23 with the R1 fix).
Sub-64-byte inputs take the identical stack path as before (I0-I4, I6, I7
unchanged and green both sides).
