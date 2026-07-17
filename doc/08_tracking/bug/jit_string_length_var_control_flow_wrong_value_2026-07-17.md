# JIT: `.length()` (not `.len()`) returns 0.0, and var reassigned in a loop/branch returns nil from string methods

- **Date:** 2026-07-17
- **Severity:** P2 (silent wrong result in compiled/JIT code; correct in interpreter)
- **Status:** FIXED (lane S29, 2026-07-17). Root cause was NOT in codegen
  dispatch (that part was already correct and identical for `len`/`length`
  everywhere) — it was a missing alias in HIR return-type inference. See Root
  Cause / Resolution below.
- **Area:** HIR method-call return-type inference (Rust seed,
  `src/compiler_rust/compiler/src/hir/lower/expr/mod.rs`), which starves the
  shared MIR arg-boxing step (`lowering_expr_builtin.rs`) of the correct
  static type for `.length()`. Cranelift JIT is the only backend that visibly
  breaks; the "var reassigned in a loop returns nil" symptom is the SAME
  root cause, not a separate var-type-tracking defect (verified: `.len()` on
  the identical loop/reassignment repro already returns the correct value
  1,1,1 — see Root Cause below).

## Root Cause

`.length()` IS a documented, fully-supported synonym for `.len()` — every
codegen table already treats them identically:
- `src/compiler_rust/compiler/src/codegen/instr/methods.rs:252` `("String","len")|("String","length") => rt_string_len`
- `src/compiler_rust/compiler/src/codegen/instr/closures_structs.rs:67,1101` `is_bare_builtin_collection_method` and the qualified-dispatch map both list `"len" | "length"`
- `src/compiler_rust/compiler/src/codegen/instr/calls.rs:2707,3133` `sffi_alias_target`: `"len" | "length" => Some("rt_len")`
- `src/compiler_rust/compiler/src/interpreter_helpers/method_dispatch.rs:33`,
  `interpreter_method/string.rs:21`, `interpreter_method/collections.rs` (×3):
  all match `"len" | "length"` identically.

The ONE place that forgot the alias was HIR method-call return-type
inference in `src/compiler_rust/compiler/src/hir/lower/expr/mod.rs`
(function `lower_builtin_method_call`, three tables):
- string methods: line 899 (was `"len" => Some(TypeId::I64)`, no `"length"`)
- array methods: line 923 (same gap)
- Any/Dict methods: line 985 (`"len" | "size"`, no `"length"`)

Because none of these tables recognized `"length"`, `lower_builtin_method_call`
returned `Ok(None)` for it, and the caller `lower_method_call` (line ~627)
fell through to the generic path: `ty: self.lookup_method_return_type(recv_ty, "length")`,
which (finding no user-defined `.length` method anywhere) returns
`TypeId::ANY` as its final fallback (line 728). So the HIR expression
`s.length()` was typed `ANY` instead of `I64`, even though the receiver's
static type (`String`) was known correctly the whole time — confirming the
bug doc's own MIR observation ("the receiver IS loaded and passed
correctly").

That wrong static type (`ANY` instead of `I64`) is what corrupts the VALUE,
not the dispatch: `print()`'s argument-boxing step in MIR lowering
(`src/compiler_rust/compiler/src/mir/lower/lowering_expr_builtin.rs:277-283`,
`needs_int_boxing = matches!(arg.ty, TypeId::I16|I32|I64|U8|U16|U32|U64)`)
inserts a `BoxInt` instruction to tag a raw scalar as a proper
`RuntimeValue` before it reaches `rt_println_value`. For `.len()` (`arg.ty ==
TypeId::I64`) this fires correctly. For `.length()` (`arg.ty == TypeId::ANY`)
it is skipped — `ANY` is assumed to already be a tagged `RuntimeValue` — so
the RAW, untagged `i64` returned by `rt_len` (e.g. `2`) is passed straight to
`rt_println_value`, which misdecodes its low tag bits as a different runtime
type and prints garbage (`0.0` for strings, a blank line for arrays,
`<value:0xN>`/`nil` depending on the raw bit pattern and control-flow
context — matching every symptom in this doc, including the `var`-in-loop
`nil` case, which is the identical mechanism, not a separate var
type-tracking bug: `.len()` on the exact same loop/reassignment repro already
returns the correct value on every iteration).

This explains why native-build (LLVM AOT) was unaffected: the LLVM codegen
backend does not solely trust the shared MIR arg-boxing decision for
`rt_len` results (it already produces "2\n2" for both spellings before this
fix), while Cranelift's print path does trust it — making this a
Cranelift-only-visible symptom of a backend-agnostic HIR bug.

An orthogonal check confirms the "unknown method" fallthrough class is
already loud and did NOT need fixing: `s.lenggth()` (a genuinely unknown
method) produces `Runtime error: Function 'str.lenggth' not found` plus a
literal `error` print — a clear diagnostic, not a silent 0/nil. So this bug
is narrowly the missing `"length"` alias in HIR return-type inference, not
a generic unresolved-method-silently-returns-default class.

## Resolution

Added `"length"` alongside `"len"` in the three HIR return-type-inference
match arms in `src/compiler_rust/compiler/src/hir/lower/expr/mod.rs` (now at
lines 911, 936, 999 after the added comments), matching what every codegen
and interpreter table already did. This restores `TypeId::I64` typing for
`.length()`, which makes the print-argument boxing step (and any other
future consumer that depends on the static type of a method-call result)
handle `.length()` identically to `.len()`.

Verified (see `build/s29_report.md` for full transcript): rebuilt the Rust
seed driver from source (`CARGO_TARGET_DIR=build/cargo_s29`, `cargo build -p
simple-driver --bin simple`) and re-ran the Cranelift JIT probes directly
against the freshly built binary — `.length()` on strings/arrays/dicts and
the var-reassigned-in-a-while-loop repro all now match the interpreter's
correct values, `.len()` is unchanged, and `s.lenggth()` still errors loudly.

**Not in scope / noted for a future lane:** the pure-Simple self-hosted
compiler (`src/compiler/`) has the identical `"len"`-only gap in several
places (e.g. `10.frontend/core/compiler/cg_expr.spl:500`,
`cg_helpers.spl:267`, `10.frontend/core/interpreter/eval_methods.spl` ×3,
`access_literal_assign_eval.spl:23`, `call_method_eval.spl:715`), while two
other pure-Simple files (`50.mir/_MirLoweringExpr/expr_dispatch.spl`,
`method_calls_literals.spl`) already correctly handle `"len" | "length"`
together. Traced (not assumed) that these specific gap sites are dormant
for `bin/simple native-build`: `cg_expr`/`cg_method_call_expr` is only ever
called from `c_codegen.spl` (a separate C-source-transpilation backend, not
the LLVM/Cranelift path native-build uses), and the `eval_*` sites belong to
the tree-walking interpreter. Empirically, pre-fix `native-build` already
returned the correct `.length()` value — if these sites were live on that
path, that run would have reproduced the bug. `bin/simple` in this worktree
also currently resolves to the Rust seed binary, not the self-hosted
compiler. So this latent gap is confirmed out of scope for the
reported/reproduced bug and was left untouched — flagging it here so a
future self-host redeploy or C-transpile/interpreter consumer doesn't
reintroduce this symptom.

## Symptom

Reproduced against the current deployed seed binary
(`bin/release/x86_64-unknown-linux-gnu/simple`, via `bin/simple run`):

```
fn main():
    val s = "aa"
    print(s.len())        # correct: 2
    print(s.length())      # WRONG: 0.0 (should be 2)
```

`--emit-mir` on the `.length()` repro shows a perfectly-formed
`MethodCallStatic { receiver: <loaded vreg>, func_name: "str.length", args: [] }`
— the receiver IS loaded and passed correctly (this is NOT the receiver-fold
bug in `jit_string_method_on_var_receiver_folds_2026-06-13.md`). The wrong
`0.0` output must come from further down the codegen/runtime dispatch for
`length` specifically (as opposed to `len`, which is correct), or from a
print-formatting bug that only triggers for whatever value/type `length`
produces.

Separately, a `var` string reassigned inside a `while` loop returns `nil`
from `.length()` on every iteration, where the interpreter correctly returns
the reassigned string's length:

```
fn main():
    var s = "aa"
    var i = 0
    while i < 3:
        s = "d"
        print(s.length())   # JIT: nil, nil, nil    interp: 1, 1, 1
        i = i + 1
```

Interpreter (`SIMPLE_EXECUTION_MODE=interpret`) gives the fully-correct
reference trace for a combined repro
(`var s = "aa"; print(s.length()); s = "bbbbb"; print(s.length());
print(s.char_at(0)); if true: s = "ccccccc"; print(s.length()); ...loop...`):
`2, 5, b, 7, 1, 1, 1`. The JIT/compiled path gives:
`0.0, <value:0x5>, b, <value:0x7>, nil, nil, nil` — the `<value:0x5>` /
`<value:0x7>` entries are a `print` display quirk (the underlying value is
correct: 5 and 7), but the initial `0.0` and the loop's `nil, nil, nil` are
genuinely wrong.

## Scope note

This is explicitly a DIFFERENT defect from
`jit_string_method_on_var_receiver_folds_2026-06-13.md` (which is about an
uppercase-first-letter receiver identifier being folded into the call NAME by
an old parser heuristic — already fixed in source, pending redeploy). This
new bug reproduces with lowercase receiver names, where MIR already shows the
receiver correctly preserved, so the fold-into-name mechanism is not in play
here at all.

## Fix direction (not investigated)

Not root-caused. Suggested starting points for a future lane:
- Compare codegen handling of `"len"` vs `"length"` in
  `try_compile_builtin_method_call` (`src/compiler_rust/compiler/src/codegen/instr/closures_structs.rs`)
  and in `codegen/instr/calls.rs`'s qualified-method map — both list
  `"len" | "length" => "rt_len"` / `Some("rt_len")` identically, so if they
  really dispatch the same way the bug may be in how the *result* of
  `rt_len`/`inline_runtime_len_value` gets typed/boxed specifically when
  reached via the `.length()` spelling vs `.len()` (print may be
  misinterpreting an int result as a float in one path but not the other).
- For the loop/branch `nil` result: check whether a `var`'s recovered/tracked
  type (`recover_receiver_type`, MIR local-type table) gets invalidated or
  set to something non-string once the local is reassigned inside a loop
  body, causing the builtin-method dispatch to miss the string-method table
  and fall through to a path that returns nil.
- Add JIT/AOT regression tests once fixed: `val s = "aa"; assert s.length() ==
  2` and a `var` reassigned inside `while`/`if` with `.length()`/`.char_at()`
  checked after each assignment.
