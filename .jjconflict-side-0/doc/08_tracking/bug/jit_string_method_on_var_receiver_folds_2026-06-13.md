# JIT: string method call on a local/global VARIABLE receiver returns empty/garbage

- **Date:** 2026-06-13
- **Severity:** P1 (silent wrong result in compiled/JIT code; correct in interpreter)
- **Status:** FIXED AT SOURCE TIP, PENDING REDEPLOY (2026-07-17) — root cause is a
  Rust-seed **parser** heuristic (not MIR lowering/type inference as originally
  suspected); already removed by commit `4802c92768c` (2026-07-13,
  "fix(native-build): preserve primitive method dispatch"), which is an ancestor
  of current tip. The bug still reproduces against the currently-deployed seed
  binary (`bin/release/x86_64-unknown-linux-gnu/simple`) only because that
  binary predates the fix. See "Fix-lane verification" section below.
- **Area:** parser postfix-call disambiguation (`src/compiler_rust/parser/src/expressions/postfix.rs`)
  — NOT mir/lower as originally suspected; see corrected root cause below.

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

## Root cause (verified 2026-06-13; CORRECTED 2026-07-17 fix-lane s21)

The MIR for `T.char_at(0)` is `Call { target: Pure("T.char_at"), args: [idx] }`
— the **receiver `T` is folded into the call NAME**, not loaded and passed as
arg[0]. Codegen's qualified-method map (`codegen/instr/calls.rs`) splits
`"T.char_at"` → method `char_at` → `rt_string_char_at` and calls it with `args`
(just `[idx]`), so the runtime fn runs with **no receiver string** → empty/-1.
(Confirmed still true today, byte-for-byte, via `bin/simple compile --emit-mir`
against the currently-deployed seed — see Fix-lane section.)

Originally this was attributed to "the receiver's type not being known as
`text`" during MIR lowering / type inference. **That diagnosis was wrong.**
The actual trigger, found by the 2026-07-17 fix lane via direct MIR
comparison, is **the receiver identifier's first letter being uppercase**:

| receiver | result | why |
|----------|--------|-----|
| string **literal** `"x".char_at()` | ✓ works | receiver is an arg |
| **param** `s: text` then `s.char_at()` | ✓ works | typed param → loaded as receiver |
| local `val T = "x"` then `T.char_at()` (uppercase name) | ✗ empty | receiver name starts uppercase → parser misclassifies as `Type.method` static call |
| local `val myStr = "x"` then `myStr.char_at()` (lowercase name) | ✓ works | parser correctly emits `MethodCall`; MIR shows `MethodCallStatic { receiver: <loaded vreg>, func_name: "str.char_at", .. }` |
| module `val TABLE: text` then `.char_at()` (uppercase name) | ✗ empty | same uppercase-name fold (explicit `: text` does NOT help — the parser decision happens before any type is known) |
| module `val enc_table: text` then `.char_at()` (lowercase name) | ✓ works | same fix applies uniformly to module globals |
| **array** var `a.len()` / `a.push()` | ✓ works | array methods use dedicated MIR paths |

So it was never really about `text` type inference — it was the PARSER's old
`is_type_path()` heuristic (`name.chars().next().is_uppercase()`) in
`src/compiler_rust/parser/src/expressions/postfix.rs`, which decided, purely
from the receiver's spelling, whether `recv.method(args)` should parse as
`Expr::MethodCall` (receiver loaded normally) or as `Expr::Call{ callee:
Expr::Path([recv, method]) }` (a static/qualified call, receiver discarded).
Any `val`/`var`/module constant with an uppercase first letter (a common
Simple naming convention, e.g. `T`, `TABLE`, `ENCODE_TABLE`) tripped the
static-call branch, and when the name did not resolve to a real registered
type it fell through to a bare `Global("Name.method")` call — reproducing
exactly the MIR shown above. `print(T)` and `T + "x"` were unaffected because
those never go through postfix method-call parsing.

This heuristic and its only call site were **removed** by commit
`4802c92768c` ("fix(native-build): preserve primitive method dispatch",
2026-07-13): `recv.method(args)` now unconditionally parses as
`Expr::MethodCall`, and the value-vs-type decision is deferred to
HIR/interpreter lowering (which resolves it correctly via the local/global
symbol table, not by looking at capitalization).

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

~~Either (a) infer `text` for `val x = <string-expr>`... or (b) in MIR
lowering of `ident.method(args)`, always lower `ident` to a receiver vreg~~
— superseded: the actual fix (already landed, see below) was at the
**parser**, not MIR lowering: `src/compiler_rust/parser/src/expressions/postfix.rs`
now always parses `recv.method(args)` as `Expr::MethodCall` regardless of the
receiver identifier's capitalization, removing the `is_type_path()` heuristic
that used to reclassify uppercase-starting receivers as static `Type.method`
calls. Add a JIT/AOT regression test: `val T = "ABCDEF"; assert T.char_at(0)
== "A"` and `T.length() == 6` (uppercase name specifically, to guard the
regression this bug was about).

## Fix-lane verification (2026-07-17, lane s21)

Worktree reset to origin tip `2e1ba67511c`. Confirmed via
`git merge-base --is-ancestor 4802c92768c 2e1ba67511c` (exit 0) that the fix
commit is already included, and via
`grep -rn "is_type_path" src/compiler_rust/parser/src/expressions/*.rs`
(zero hits) that the old heuristic and its only call site no longer exist
anywhere in the parser.

Because the deployed seed binary
(`bin/release/x86_64-unknown-linux-gnu/simple`, reached via the `bin/simple`
symlink) predates commit `4802c92768c`, the bug still reproduces end-to-end
today for uppercase receiver names — used `bin/simple compile <f> --emit-mir`
to inspect the actual MIR generated by that binary for four variants:

| receiver | MIR shape (from deployed binary) | runtime output |
|---|---|---|
| `val T = "ABCDEF"` (local, uppercase) | `Call { target: Pure("T.char_at"), args: [idx] }` — receiver never loaded | empty / `<value:0xffffffffffffffff>` (matches doc exactly) |
| `val myStr = "ABCDEF"` (local, lowercase) | `MethodCallStatic { receiver: <loaded vreg>, func_name: "str.char_at", args: [idx] }` | `A` / `6` (correct) |
| `val TABLE: text = "ABCDEF"` (module global, uppercase) | `Call { target: Pure("TABLE.char_at"), .. }` — same fold | empty / `<value:0xffffffffffffffff>` |
| `val enc_table: text = "ABCDEF"` (module global, lowercase) | `MethodCallStatic { receiver: <loaded vreg>, func_name: "str.char_at", .. }` | `A` / `6` (correct) |

This is conclusive: the fold is gated purely on the receiver name's first
letter, exactly matching the parser `is_type_path()` heuristic that was
removed in current source. No further Rust-seed source change is needed for
**this** bug — the fix is already committed and only needs the pending seed
redeploy to take effect for real users.

No `src/` diff was produced by this lane for this ticket (git status clean
before and after investigation) — the deliverable is this doc correction plus
the new bug filed below.

### Separate defect found during mandatory verification (NOT part of this bug, filed separately)

While verifying "reassignment in branches/loops" per this lane's mandate,
found that `var`/`val` **lowercase** receivers (i.e., NOT hitting the bug
above) still print wrong results for `.length()` specifically (`.len()` is
fine — `val s = "aa"; print(s.len())` correctly prints `2`, but
`print(s.length())` prints `0.0`), and that a `var` string reassigned inside a
`while` loop returns `nil` from `.length()` on every iteration where the
interpreter correctly returns `1`. MIR for the minimal `.length()` repro
already shows a fully correct `MethodCallStatic` with the receiver loaded —
so this is a distinct runtime/codegen defect in the `length` (vs `len`)
dispatch path and in var type-tracking across control flow, unrelated to the
receiver-folding parser bug this doc tracks. Filed as
`doc/08_tracking/bug/jit_string_length_var_control_flow_wrong_value_2026-07-17.md`;
not fixed in this lane (out of scope, budget).

## Relationship to other bugs

- This is a DISTINCT bug from `stage4_imported_const_compare_2026-06-12.md`
  (that one is `tag == IMPORTED_CONST` comparison misevaluation). The base64
  "module text const empty" symptom is THIS bug (receiver fold), not global-init
  ordering — `__module_init` does run and materialize the string.
- Pre-existing: reproduces on the pre-session seed (not introduced by the
  2026-06-13 str.bytes/JIT-guard/flatten work).

## Runtime verification (2026-07-17)

Probed with exact repro: `val T = "ABCDEF"` then `T.char_at(0)` → empty, `T.length()` → `<value:0xffffffffffffffff>`. `TABLE.char_at(0)` (module-level) also → empty. All three results match documented table exactly. No JIT-failure message printed (ran through working JIT path and mis-compiled silently, consistent with root cause analysis).
