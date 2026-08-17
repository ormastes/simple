# Bug: enum associated functions (`impl Enum:` and enum-body `static fn`) — scoping study, not fixed

- **Date:** 2026-07-29
- Status: OPEN (P1)
- Status re-verified 2026-08-17 by source inspection (triage shard 01).
- **Severity:** critical (silent wrong values on the default JIT engine; a second,
  narrower, independent false-rejection defect on the interpreter)
- **Binary under test:** Rust seed `src/compiler_rust/target/debug/simple`,
  built by this lane with `cargo build -p simple-driver --bin simple`,
  **mtime 2026-07-29 01:05:36 UTC**, exit 0, warnings only (unrelated
  `unused_assignments` in `interpreter_call/block_execution.rs`). No other
  `src/**` file was modified by this lane except this doc and the `.spipe`
  state note.
- **Parent bugs:**
  `doc/08_tracking/bug/enum_associated_fn_never_called_on_jit_2026-07-28.md`,
  `doc/08_tracking/bug/enum_assoc_fn_residual_exposure_2026-07-28.md`.
- **Prior guard:** `362b206e7e4` (`mir/lower/lowering_expr_call.rs`) — turns an
  *undeclared* `EnumName.member` from a silent bogus value into a hard error.
  It intentionally does not touch the *declared*-method case. This lane
  determines what fixing the declared case would actually require.

## 1. The exact boundary — four minimal repros, one fresh binary

All four probes at `/tmp/enum_probe/{a_impl_static,b_body_static,c_body_method,mod_a,d_cross_module}.spl`
(scratch, not committed — recreate from the snippets below if needed). One
construct per probe file, run with `bin` = the binary described above,
`SIMPLE_EXECUTION_MODE=interpreter` for the interpreter row, 20s timeout,
`$?` read from the command under test, output captured to files and tails
read back.

| # | Form | JIT (default) | Interpreter |
|---|---|---|---|
| (a) | `static fn` inside `impl E1:` block, **same file** as the call | `got NOTHING` — fabricated, matches no arm | **`error: semantic: unknown variant or method 'make' on enum E1`, exit 1 — false rejection** |
| (b) | `static fn` inside the enum body itself (`enum E2: … static fn make() …`), same file | `got NOTHING` — identical fabrication | `got B` — **correct** |
| (c) | plain (non-static) method inside the enum body, called as `instance.method()` | `isB` — correct | `isB` — correct |
| (d) | `static fn` inside `impl TD:` block, but **TD is imported from a separate module** (`use mod_a.TD`) | `got NOTHING` — identical fabrication | `got Float` — **correct** |

Repro bodies (each is the entire file):

```
# a_impl_static.spl
enum E1:
    A
    B
impl E1:
    static fn make() -> E1:
        E1.B
fn main():
    val x = E1.make()
    match x:
        case E1.A: print "got A"
        case E1.B: print "got B"
        case _:    print "got NOTHING"
```

```
# b_body_static.spl — same as (a) but `static fn make()` moved inside `enum E2:` body, no impl block
```

```
# c_body_method.spl — enum E3 with `fn label(self) -> text:` in the body,
# called as `E3.B.label()` via an instance, not a type-qualified call
```

```
# mod_a.spl: enum TD (Int/Float/Text) + impl TD: static fn from_text(s) -> TD
# d_cross_module.spl: use mod_a.TD ; TD.from_text("float") ; match
```

### What this establishes

1. **The JIT defect is not about `impl` vs enum-body, and not about same-file
   vs cross-module.** All three JIT-broken forms ((a), (b), (d)) fabricate
   identically. This matches the HIR registration code (§3): `impl Enum:`
   methods and enum-body `static fn`s are registered into the exact same
   `self.globals["EnumName.method"]` map, by the exact same shape of code, so
   there is no distinguishing signal available to the MIR lowering guard
   between them. **Any fix must treat (a) and (b) uniformly — there is no
   smaller fix that special-cases "impl block only."**
2. **Case (c) is a different code path entirely and was never at risk.**
   `instance.method()` lowers through `lower_method_call_expr` (receiver
   dispatch), never through `lower_call_expr`'s `HirExprKind::Global("Enum.…")`
   branch where the fabrication lives. This is why earlier probing found
   enum-body plain methods unaffected — it's not that plain methods are safer,
   it's that they're on a different lowering path altogether.
3. **A second, independent, narrower interpreter bug exists**, previously
   undocumented: the interpreter is **correct** for enum-body statics (b) and
   for cross-module `impl` statics (d), but **incorrectly rejects** a
   same-file/entry-script `impl Enum:` static (a) as if `make` were never
   declared. This exactly reproduces the task's motivating example
   (`TD.from_text` "rejected outright") — but only holds for the same-file
   case; the earlier `enum_associated_fn_never_called_on_jit_2026-07-28.md`
   doc's `E1.make()` example (which reported the interpreter as correct) must
   have been declared in a form matching (b) or (d), not (a) — the two docs
   are not actually in conflict, they were measuring different forms.

## 2. Interpreter root-cause sketch (new finding, not fully bisected)

`src/compiler_rust/compiler/src/interpreter/expr/calls.rs:608-677` resolves
`EnumName.field` in order: declared variant → `enum_def.methods` (enum-body,
this is why (b)/(c) work) → `impl_methods.get(enum_name)` (module-local impl
registry) → `GLOBAL_IMPL_METHODS` (cross-module fallback, this is why (d)
works) → error. Both `impl_methods` and `GLOBAL_IMPL_METHODS` are populated
generically for any `Node::Impl` (struct/class/enum alike, no type-kind
branch) in `src/compiler_rust/compiler/src/interpreter_eval.rs:862-932`. That
code looks correct and target-agnostic on inspection, which means the gap for
case (a) is upstream of it — most likely the **entry-script execution driver**
(`driver/src/interpreter.rs:100 run()` → `self.runner.run_source(code)`,
distinct from the module-import loader that (d) exercises) either doesn't run
this registration pass at all for the file passed directly to `bin/simple run`,
or runs it in an order where `main()`'s call is evaluated before the impl
block is registered. **Not bisected further in this lane** — flagging as the
next concrete step rather than guessing at a line number.

## 3. Where the JIT goes wrong (confirmed, precise)

`src/compiler_rust/compiler/src/mir/lower/lowering_expr_call.rs`:

- Lines 445-454: the `362b206e7e4` guard. It errors only when `enum_name`
  positively resolves to an enum AND `variant_name` is positively **not** a
  declared variant AND the dotted name is absent from **both**
  `self.global_types` and `self.available_functions`. When the name *is* in
  `global_types` (i.e. it's a real impl-declared or enum-body-declared
  static), the guard is correctly silent — **it does not error, but it also
  does nothing to route the call correctly.**
- Lines 456-583: immediately after, `is_enum && !arg_regs.is_empty()` (456)
  and plain `is_enum` (572) unconditionally emit `MirInst::EnumWith` /
  `MirInst::EnumUnit` for **any** dotted call whose head resolves to a known
  enum — with **no check at all** against `global_types` or
  `available_functions`. This is the actual fabrication site. It hashes
  `variant_name` into a discriminant via `EnumUnit`/`EnumWith`'s runtime
  encoding regardless of whether `variant_name` is a real declared function.
- Confirms `enum_associated_fn_never_called_on_jit_2026-07-28.md`'s "likely
  cause" section, but pins the exact lines: the guard and the fabrication
  branch are **not the same code** — the guard was added without also gating
  the fabrication branch it was meant to guard.
- **Adjacent, separately-broken path, not covered by `362b206e7e4` at all:**
  `src/compiler_rust/compiler/src/mir/lower/lowering_expr_ident.rs:36-50`
  fabricates `EnumUnit` for a bare (non-call) `EnumName.field` reference using
  only `is_known_enum_type_for_variant`, with no `enum_declares_variant`
  check whatsoever — not even the narrower undeclared-name protection that
  calls now have. Out of scope for this task's three call forms, but it's
  the same class of bug and unguarded even for the *simpler*, already-fixed
  undeclared-name case.

### HIR registration confirms (a) and (b) are structurally identical

`src/compiler_rust/compiler/src/hir/lower/module_lowering/module_pass.rs`:
- Lines 398-407 (enum body, form b): for each `method` in `e.methods`, inserts
  `self.globals["EnumName.method"] = ret_ty`.
- Lines 412-425 (`impl` block, form a): for each `method` in
  `impl_block.methods` when the target type name resolves, inserts the exact
  same `self.globals["EnumName.method"] = ret_ty`.

Byte-for-byte the same registration shape. There is no field distinguishing
"came from an enum body" vs "came from an impl block" once it's in
`global_types` — so a fix that special-cased `impl` blocks would need to
invent a distinction the compiler currently throws away, for no benefit
(since both forms need the same fix).

## 4. The 151-site claim — NOT VERIFIED, closest real numbers are far smaller

Grepped `src/compiler/00.common/config.spl` (394 lines) directly, three ways,
none of which approaches 151:

| Measurement | Count |
|---|---|
| All `CapWord.lowercase_method(` call sites in the file (any receiver, enum or not) | **12** |
| Of those, real enum-associated-function calls (`TypeDefault.from_text` ×4, `CompilerProfile.from_text` ×2) — matches `enum_assoc_fn_residual_exposure_2026-07-28.md`'s own count of 6 for this exact file | **6** |
| Repo-wide (`src/`, `doc/`, excluding vendor) call sites referencing this file's two enums (`CompilerProfile.`, `TypeDefault.`) by name, any file | **53** |

None of these interpretations reaches 151 by close to an order of magnitude
in the small-count directions, nor matches it from the large-count direction
either (the parent residual-exposure doc's own repo-wide totals are 146
high-confidence real sites and ~1611 mostly-false-positive ambiguous sites —
151 doesn't line up with either boundary). **I could not reconstruct 151
under any grep interpretation tried and could not find a saved artifact
producing it.** Treat the number as unverified; the real, checked scope for
`config.spl` itself is 6 real associated-fn call sites (2 enums,
`CompilerProfile` and `TypeDefault`).

More importantly: **the premise "extending the guard" is the wrong framing.**
The guard at lines 445-454 already exempts `global_types`-registered names —
extending its *rejection* condition to also cover `impl Enum:` statics would
not by itself change any behavior, because that condition already treats
`impl`-declared and enum-body-declared statics identically (see §3's HIR
finding). **The guard was never the site that needs to change.** The actual
minimal code change is reusing the guard's *existing* `global_types` /
`available_functions` check to also gate the **fabrication** branches (lines
456 and 572) — i.e., skip `EnumUnit`/`EnumWith` emission and fall through to
the normal `MirInst::Call { target: CallTarget::from_name(name) }` path
(lines 592-639, the same path `Box.make()`-style class statics already use
successfully) whenever the dotted name resolves to a real global function.
This does not widen any error surface — every currently-passing call site
keeps passing (variants stay variants; only names present in `global_types`
stop being misfabricated). So the "151 sites go red" framing describes a
different, more aggressive change (turning the guard into a stricter
rejection) than the change actually needed (redirecting the fabrication
branch to the pre-existing normal call path for names already known to be
real functions).

## 5. Fix shape and blast radius

Two **independent** defects, in different subsystems, each individually
small in code-diff terms but **not small in verification cost**:

**JIT (MIR lowering) fix** — small diff: gate lines 456 and 572 in
`lowering_expr_call.rs` with the same
`!self.global_types.contains_key(name.as_str()) && !self.available_functions.contains(name.as_str())`
condition already used at line 447-448, falling through to the existing
generic-call path when it's false. Roughly 4-6 changed lines.

**Interpreter fix** — unknown diff size, because the root cause is not yet
bisected past "somewhere upstream of `interpreter_eval.rs`'s `Node::Impl`
handling, specific to how `bin/simple run <entry-file>.spl` differs from
import-triggered module evaluation." Could be a one-line ordering fix or a
structural gap in the entry-script driver; not knowable without more digging
in `driver/src/interpreter.rs` and whatever function `run_source`/
`run_source_in_memory` calls for direct-script mode vs `use`-triggered
loading.

**Why neither should be landed in this lane:**
- The task's own bar is "full rebuild, both-engine verification, regression
  sweep vs a TRUE baseline" before landing. A regression sweep credible enough
  to trust here is multi-hour work (the parent `enum_assoc_fn_residual_exposure`
  doc's own sweep tooling took a full session and still left 79 ambiguous
  receiver names unresolved).
- The two defects are in different engines with different (and only partly
  understood, for the interpreter) root causes. Fixing only the JIT half
  would leave the two engines *newly* disagreeing in the opposite direction
  for form (a) specifically (JIT would start returning `B` correctly while
  the interpreter still rejects it) — an improvement, but still a
  cross-engine inconsistency that the "both-engine verification" bar exists
  to catch, and landing it without also closing the interpreter gap invites
  someone to `SIMPLE_EXECUTION_MODE=interpreter` fallback into the *other*
  wrong answer.
- `src/compiler_rust/` is confirmed only lightly contended right now (one
  unrelated file, `runtime/src/value/sffi/io_print.rs`, modified by a
  concurrent session) — so contention is not the blocker; verification depth
  is.

## 6. Recommended sequencing

1. **JIT fix first.** It is well-understood, small, and self-contained: gate
   the two fabrication branches with the guard's existing condition. Verify
   with all four repros above plus a rerun of
   `enum_assoc_fn_residual_exposure_2026-07-28.md`'s probes #1-#3 (`Platform.from_u8`,
   `CompileMode.from_text`, `SdnValue.int`) to confirm they now return correct
   values instead of `NOTHING`/wrong-arm — those are the real production
   call sites already inventoried, so re-checking them is cheap and high-signal.
2. **Bisect the interpreter gap second**, using probes (a) vs (d) as the
   minimal differential (same construct, only same-file-vs-imported differs).
   Whatever the entry-script driver does differently from the import loader
   is the fix site.
3. **Only then run the full bootstrap + regression sweep** the task's
   verification bar requires, covering both fixes together so the two
   engines are never landed newly-inconsistent with each other mid-sequence.
4. Do not extend `362b206e7e4`'s error guard scope as part of this — per §4,
   it does not need to change; only the fabrication branches do.

## Artifacts

Probes at `/tmp/enum_probe/` (scratch, not committed):
`a_impl_static.spl`, `b_body_static.spl`, `c_body_method.spl`, `mod_a.spl`,
`d_cross_module.spl`, plus `.jit.out`/`.interp.out` pairs and `results.txt`
(exit codes). Binary: `src/compiler_rust/target/debug/simple`, built by this
lane, mtime 2026-07-29 01:05:36 UTC.

## Update 2026-08-17 — DOES NOT REPRODUCE on the JIT; closing the JIT claim

Both this doc and its sibling (`enum_associated_fn_never_called_on_jit_2026-07-28`
/ `enum_impl_static_fn_scoping_2026-07-29`) assert that a declared enum
associated fn yields a silent wrong value under the JIT. **That is no longer
true.** These two rows collapse into one finding.

Gate spec both docs name, run on the deployed seed:

```
test/shared/control_flow/static_fn_spec.spl
SPEC FILE VERDICT: declared>=26 executed=26 passed=26 failed=0 dropped=0
Results: 26 total, 26 passed, 0 failed
```

executed=26, so the run is non-vacuous, not a silent exit-0.

Direct probe — the bodies genuinely execute and the values are correct:

```simple
enum Col: Red; Blue
impl Col:
    fn make() -> Col: print("BODY RAN"); Col.Blue
    fn tag() -> i64:  print("TAG BODY RAN"); 7
```

JIT: `BODY RAN` / `is_blue=true` / `TAG BODY RAN` / `t=7`.

**Measurement trap worth recording:** an earlier pass of this probe printed
`c => <enum@0x4da548111a0>` and was very nearly filed as "returns a bogus
value". That string is just `to_text()`'s formatting of an enum value — the
value itself is correct, as `c == Col.Blue` -> `true` shows. Asserting on a
`to_text()` rendering rather than on the value is how a correct enum gets
reported as garbage.

**Remaining live defect, out of scope for this batch:** the *interpreter* still
rejects the same program outright —
`error: semantic: unknown variant or method 'make' on enum Col`, exit 1. That is
a real gap, but it is **loud** (non-zero exit, explicit diagnostic), not a
silently-wrong result, and it lives in
`src/compiler/10.frontend/core/interpreter/**`, which is claimed by another lane.
Not fixed here; flagged for that lane.

**Action:** JIT claim -> FIXED (does not reproduce). Interpreter gap re-filed as
the surviving issue.
