# JIT: string method call on a local/global VARIABLE receiver returns empty/garbage

- **Date:** 2026-06-13
- **Severity:** P1 (silent wrong result in compiled/JIT code; correct in interpreter)
- **Status:** Open — root-caused, fix is in MIR lowering / type inference (not yet done)
- **Area:** mir/lower method-call receiver resolution + local/global type inference (cranelift + AOT)

## Symptom

A string method (`char_at`, `length`, `bytes`, `chars`, `len`, …) called on a
**local `val`** or a **module-level** string variable returns empty/garbage in
JIT/AOT, while correct in the interpreter:

```
fn main():
    val T = "ABCDEF"
    print(T.char_at(0))   # JIT: (empty)              interp: A
    print(T.length())     # JIT: <value:0xffff…> (-1) interp: 6
```

Module-level is the same bug (not special):
`val TABLE: text = "ABCDEF"; TABLE.char_at(0)` → empty in JIT.

## Root cause (verified)

The MIR for `T.char_at(0)` is `Call { target: Pure("T.char_at"), args: [idx] }`
— the **receiver `T` is folded into the call NAME**, not loaded and passed as
arg[0]. Codegen's qualified-method map (`codegen/instr/calls.rs:~2986`) splits
`"T.char_at"` → method `char_at` → `rt_string_char_at` and calls it with `args`
(just `[idx]`), so the runtime fn runs with **no receiver string** → empty/-1.

The trigger is **the receiver's type not being known as `text`** at lowering:

| receiver | result | why |
|----------|--------|-----|
| string **literal** `"x".char_at()` | ✓ works | receiver is an arg |
| **param** `s: text` then `s.char_at()` | ✓ works | typed param → loaded as receiver |
| local `val T = "x"` then `T.char_at()` | ✗ empty | type not inferred as text → folded into name |
| module `val TABLE: text` then `.char_at()` | ✗ empty | same fold (explicit `: text` does NOT help) |
| **array** var `a.len()` / `a.push()` | ✓ works | array methods use dedicated MIR paths |

So it is **string-method-on-identifier-receiver** specific. `print(T)` and
`T + "x"` work (those load T's vreg normally) — only the method-call syntax
folds the receiver.

## Impact

- `std.common.base_encoding.base64.base64_encode` returns empty in JIT — its
  `ENCODE_TABLE: text` lookup (`base64.spl:18`) is a module string var, and
  `ENCODE_TABLE.char_at(idx)` yields empty.
- Any compiled/JIT code doing `string_var.char_at/.length/…` is silently wrong.
  Invisible to interpreter testing.

## Workaround (CORRECT ones)

- Pass the string through a typed `text` **param**: `fn _ln(s: text) -> i64: s.length()`
  then `_ln(T)` — verified returns 6.
- Use the literal directly, or `rt_*`/free-function forms.
- Do **NOT** "use a function-local val" — local vals fail identically.

## Fix direction

Either (a) infer `text` for `val x = <string-expr>` (and propagate to module
globals) so the method-call lowering takes the typed-receiver path, or (b) in
MIR lowering of `ident.method(args)`, always lower `ident` to a receiver vreg
(arg[0]) instead of folding it into a `Pure("ident.method")` name when `ident`
resolves to a local/global binding. (b) is the more localized fix. Add a
JIT/AOT regression test: `val T = "ABCDEF"; assert T.char_at(0) == "A"` and
`T.length() == 6`.

## Relationship to other bugs

- This is a DISTINCT bug from `stage4_imported_const_compare_2026-06-12.md`
  (that one is `tag == IMPORTED_CONST` comparison misevaluation). The base64
  "module text const empty" symptom is THIS bug (receiver fold), not global-init
  ordering — `__module_init` does run and materialize the string.
- Pre-existing: reproduces on the pre-session seed (not introduced by the
  2026-06-13 str.bytes/JIT-guard/flatten work).

## Runtime verification (2026-07-17)

Probed with exact repro: `val T = "ABCDEF"` then `T.char_at(0)` → empty, `T.length()` → `<value:0xffffffffffffffff>`. `TABLE.char_at(0)` (module-level) also → empty. All three results match documented table exactly. No JIT-failure message printed (ran through working JIT path and mis-compiled silently, consistent with root cause analysis).
