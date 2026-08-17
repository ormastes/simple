# Non-binding sub-patterns inside an enum payload always match and never bind

**Date:** 2026-08-01
**Status:** RESOLVED — re-verified 2026-08-17; the "Remaining RED" is gone.

## Re-verification 2026-08-17 (partial-fix sweep, lane 1)

All three of this file's reproducer functions re-run verbatim on the deployed
seed (`bin/simple`, Rust seed dated 2026-08-16):

```
nested payload bind   -> 41   (doc recorded -1)
arm selection         ->  1   (doc recorded  0)
nested literal match  ->  7   (doc recorded -1)

Results: 3 total, 3 passed, 0 failed
```

The sub-pattern no longer "always matches"; payload sub-patterns discriminate
and bind correctly.

NOT PROVED: which commit closed it (not bisected). The doc's "NOT PROVED —
blocked by PRE-EXISTING pure-Simple-lane defects" section was not re-tested;
this pass exercised the seed lane only.

--- original filing below, kept for history ---

**Status (original):** PARTIALLY FIXED 2026-08-01 — the pure-Simple MIR lowering now
implements nested payload tests + binds (was: silently skipped / loud-fail),
and a silent no-op in the compiled stage2's in-process native lane is fixed.
See "Fix" and the CRITICAL "Engine attribution correction" sections at the
bottom: the compiled lanes users actually run (seed JIT AND `native-build
--entry`, which is the seed's `rt_native_build` codegen, NOT this repo's MIR
pipeline) REMAIN BROKEN and are Rust-side (seed not rebuildable on this host,
btrfs ENOSPC). The tree-walking interpreter was always correct.
**Severity:** CRITICAL — silent wrong values and silent wrong arm selection on the
two *compiled* engines (JIT and native LLVM); no diagnostic, exit code 0
**Affected:** `src/compiler/50.mir/_MirLoweringExpr/switch_operators_calls.spl`,
`src/compiler/20.hir/hir_lowering/expressions.spl`
**Regression spec:** `test/01_unit/compiler/enum_payload_subpattern_spec.spl`

## Symptom

Inside an enum pattern's payload, only `Binding` and `Wildcard` sub-patterns are
honoured. Every other sub-pattern kind — a nested `Enum` (`case W(A(n))`) or a
`Literal` (`case X(5)`) — is treated as **unconditionally matching** and binds
nothing:

- its **test is skipped**, so an arm fires on values it must reject, and
- its **bindings are never registered**, so names inside it read garbage.

Both are silent. The program compiles clean and exits 0 with wrong numbers.

The originally-reported shape was "nested enum-in-enum returns 0". That is real,
but it is one instance of the wider rule above — a nested **literal** is equally
broken, and the wrong value is **not reliably 0**.

## Minimal repro

```simple
enum Inner:
    A(i64)
    B(i64)

enum Outer:
    W(Inner)
    X(i64)

enum Lit:
    I(i64)

fn nested_enum_binds() -> i64:
    match Outer.W(Inner.A(41)):
        case Outer.W(Inner.A(n)): return n      # want 41
        case _: return -1

fn nested_enum_selects_right_arm() -> i64:
    match Outer.W(Inner.B(1)):
        case Outer.W(Inner.A(_)): return -1     # must NOT fire
        case Outer.W(Inner.B(_)): return 1
        case _: return -2

fn nested_literal_int() -> i64:
    match Lit.I(7):
        case Lit.I(5): return -1                # must NOT fire
        case Lit.I(7): return 7
        case _: return -2
```

Seed `run` lane (`bin/simple_seed run probe4.spl`), verbatim:

```
nested_literal_int=-1 want=7
nested_enum_binds=0 want=41
nested_enum_selects=-1 want=1
```

All three are wrong, and the process exits 0.

## Engine matrix

| sub-pattern kind in an enum payload | seed `run` (JIT) | seed `test` (interpreter) | stage2 pure-Simple native (LLVM) |
|---|---|---|---|
| `Binding` — `case E.I(n)` | OK | OK | OK |
| `Wildcard` — `case E.I(_)` | OK | OK | OK |
| `Literal` int / text / bool | **WRONG** (always-match) | OK | **WRONG** (always-match) |
| nested `Enum` — `case W(A(n))` | **WRONG** (no test, no bind) | OK | **WRONG** (no test, no bind) |

The two compiled engines fail on an **identical** set of shapes. The tree-walking
interpreter is correct, because it uses a different, fully recursive matcher
(`src/compiler_rust/compiler/src/interpreter_patterns.rs:113` `pattern_matches`,
which recurses through `pattern_matches(pat, val, ...)` per payload slot).

This is why the defect hides: the lane most people run specs on
(`bin/simple_seed test`) is the one lane that is correct.

**Evidence status.** *Measured:* the per-lane results above, from the same seed
binary on the same source — `run` is wrong and `test` is right, and swapping the
code shape (inline `print` in `main` vs one function-with-`return` per shape,
matching the spec's structure) does not change either answer, so the split is
the engine and not the shape. That `run` is the JIT lane is self-reported by the
binary (`[INFO] JIT compilation failed, falling back to interpreter`). *Read from
source:* `pattern_matches` recurses per payload slot. *Inferred:* that the `test`
lane's correctness comes specifically from that function. The inference does not
affect the defect or the fix — only the explanation of why `test` stays green.

## Shape matrix

Measured on both failing engines (`matrix.spl`, 27 checks). Identical FAIL set on
seed-JIT and stage2-native.

**Correct:**
- depth-1 binding, any arity — `E.M(a)`, `E.Two(a,b)`, `E.Three(a,b,c)`
- wildcards at the payload level — `E.I(_)`
- **outer-level sibling slots of a nested sub-pattern** — in
  `ArOut.C4(x, Ar.One(y), z)`, `x` and `z` are correct; only `y` is wrong
- top-level (non-payload) literal patterns — `match x: case 7:`
- destructuring in two steps — `case W(inner):` then a second `match inner:`
  (this is the workaround)
- **nested STRUCT sub-patterns** — `case Shape.Circle(Point(a, b)):` returns the
  correct `3, 4`. This is the useful contrast: a struct sub-pattern inside an
  enum payload works, an enum sub-pattern does not. `flatten_enum_match_arm`
  handles exactly `Tuple`/`Struct` and nothing else, which is why.

**Wrong:**
- nested enum at depth 2 and depth 3 — `W(M(a))`, `D(W(A(a)))`
- nested enum in any sibling position — first, middle, last
- nested enum with multi-arity inner payload — `C1(Two(a,b))`
- nested enum mixed with wildcards — `C2(_, Two(_, b))`
- nested enum where outer and inner variants **share a name** — `SOut.S(SIn.S(n))`
- nested enum under a guard — `case W(B(n)) if n == 9`
- **arm selection** — `case W(M(a))` fires on `W(N(...))`; a nested arm placed
  third is reached only because the earlier nested arm wrongly matched first
- nested literals in any slot — `E.Two(99, b)` fires on `E.Two(71, 72)` (and `b`
  is still bound correctly to 72, which makes it look plausible)

**The wrong value is not a stable sentinel.** Observed reads for the same
missing bind: `0` (seed JIT), `32` (stage2 native), and
`129557927575568` (stage2 native, a raw pointer). One probe shape
(`E.N(In3.A(61))`, a single-variant inner enum) **coincidentally returned the
correct 61** on stage2 native. A passing spot-check is therefore not evidence of
correctness here.

## Blast radius — the compiler miscompiles itself

`src/` (excluding vendor) contains **94** `case Variant(<literal>, ...)` sites and
**130** `case Variant(Inner(...))` call-in-payload sites. (The 130 is an upper
bound: a nested **struct** sub-pattern is genuinely supported via
`flatten_enum_match_arm`'s Tuple/Struct path, and this count cannot separate the
two statically.)

The literal count needs no such caveat, and it includes the compiler's own
constant folding — `src/compiler/35.semantics/const_eval.spl`:

```simple
# eval_if, line 570
match cond_val:
    case EvaluatedConstValue.Bool(true):     # fires for Bool(false) too
        self.eval_block(then_)
    case EvaluatedConstValue.Bool(false):
        ...

# check_const_assert, line 622
match result:
    case EvaluatedConstValue.Bool(true):     # fires for Bool(false) too
        Ok(())
    case EvaluatedConstValue.Bool(false):
        Err(ConstEvalError.AssertionFailed(msg, assert_.span))
```

Built by an affected engine, this means a compile-time `if` with a **false**
condition folds to its **then** branch, and a **failing** `static assert`
returns `Ok(())` and never fires. Also affected:
`src/compiler/70.backend/codegen_enhanced.spl:321` (`case Int(0):`) and
`src/compiler/35.semantics/macro_check/template.spl:299` (`case Group("{", _):`).

This matters for the bootstrap chain specifically: a stage-N compiler built by a
compiled (JIT or native) stage-N-1 has these arms inverted, so const-folding and
static-assert bugs can be introduced by the build rather than by the source.

## Root cause

The pattern survives the frontend intact and is dropped by the MIR consumer.

1. **Parsing is fine.** `case` patterns are parsed with the full expression
   parser (`src/compiler/10.frontend/core/parser_stmts.spl:1202`
   `parse_match_arms_common`) and converted by `convert_flat_pattern`
   (`src/compiler/10.frontend/_FlatAstBridge/convert_nodes.spl:1102`), which
   **does** recurse into payload sub-patterns. `Outer.W(Inner.A(n))` becomes
   `PatternKind.Enum("Outer","W", Tuple([Enum("Inner","A", Tuple([Binding n]))]))`.

2. **HIR lowering is fine.** `lower_pattern`'s enum branch
   (`src/compiler/20.hir/hir_lowering/expressions.spl:1192-1297`) calls
   `self.lower_pattern(pat)` on each payload sub-pattern, so the nested `Enum`
   reaches HIR with its `Binding` intact. (This is the payload walk repaired by
   `fb1a0033d51`; that fix is working — the bindings *are* defined in scope,
   which is why the arm body compiles with no "unresolved name".)

3. **MIR silently drops it.** `enum_pat_binding_syms` and
   `enum_pat_binding_positions`
   (`src/compiler/50.mir/_MirLoweringExpr/switch_operators_calls.spl:108-147`)
   walk the payload and collect only `Binding` sub-patterns:

   ```simple
   match patterns[i].kind:
       case Binding(sym, _):
           out.push(sym)
       case _:
           ()
   ```

   The `case _: ()` swallows nested `Enum` and `Literal` alike — the docstring
   says "non-Binding sub-patterns, e.g. wildcards, are skipped and simply left
   unbound", which is correct and harmless for a wildcard and silently wrong for
   everything else. `lower_enum_match`
   (`switch_operators_calls.spl:1356`) then emits a test for the **outer**
   discriminant only. Result: no inner test, no inner bind.

4. **The guard that should have caught it is bypassed.**
   `pattern_is_mir_native` (`expressions.spl:1396-1411`) returns `true` for
   `Enum(_, _, _)` **unconditionally**, so every enum arm routes to the MIR path
   above. Its own comment records that nested enum-payload destructure was
   attempted and removed, and calls the construct "unsupported, loud-fail" — but
   on the MIR path it is neither loud nor failing.

5. **The loud path exists but is unreachable for these shapes.**
   `flatten_enum_match_arm` (`expressions.spl:1637-1669`) *does* raise
   `self.error("nested match pattern kind not supported inside an enum payload
   here ... a nested Literal/Range/Or/Enum sub-pattern would need a runtime test
   with no fallthrough-to-next-arm semantics available")`. Its comment explicitly
   warns such a pattern "must not be silently treated as always-matching" —
   which is exactly what step 3 does. Because step 4 sends enum arms to MIR,
   this error never fires for them.

6. The if-chain fallback is equally blind: `pattern_test_condition`
   (`expressions.spl:1486-1547`) has **no `Enum` case** and falls to
   `case _: nil` (unconditional match); `destructure_pattern_prelude`
   (`expressions.spl:1416-1465`) has no `Enum` case either (no bindings).

The Rust seed's JIT lane fails on the same shapes, so it has an equivalent gap
in its own lowering, separate from its correct interpreter matcher.

## Why this was not fixed in this lane

- The fix is a **recursive payload test + bind** in `lower_enum_match`, which
  needs fallthrough-to-the-next-arm semantics that
  `flatten_enum_match_arm`'s comment states are **not available at that layer**.
  It is a match-lowering redesign, not a local patch.
- A previous attempt at exactly this was made and **removed** rather than
  shipped (`pattern_is_mir_native` comment), so the naive shape is known to fail.
- The seed's JIT lane needs a separate fix in Rust, and the seed **cannot be
  rebuilt on this host**: btrfs has ~1 MiB unallocated and `cargo` dies with
  ENOSPC.
- Each verification cycle on the pure-Simple lane costs a ~5-minute LLVM link
  (measured: 245s and 281s), and the pure-Simple compiler cannot self-host at
  HEAD, so a fix cannot be validated end-to-end here.

## Workaround

Destructure in two steps. This is correct on all three engines:

```simple
match outer:
    case Outer.W(inner):
        match inner:
            case Inner.A(n): ...
```

## Regression spec

`test/01_unit/compiler/enum_payload_subpattern_spec.spl` — 17 examples covering
the matrix above.

**Read its result carefully:** it **passes** today under
`bin/simple_seed test`, because that lane uses the correct interpreter. It fails
on the compiled lanes, which is where the defect lives. Until the repo's spec
runner executes on the native/JIT engine, this spec is a forward-looking guard,
not an active gate. Reproduce the actual failure with the probes below.

## Verification transcript

```
$ cd <scratch>/repro
$ bin/simple_seed run probe4.spl
nested_literal_int=-1 want=7
nested_enum_binds=0 want=41
nested_enum_selects=-1 want=1

$ <stage2>/simple native-build --source srcM --entry srcM/full.spl \
      -o fullmatrix.bin --backend llvm
Build complete: 2 compiled, 0 cached, 0 failed
$ ./fullmatrix.bin
... 15 FAIL / 12 PASS, identical FAIL set to the seed JIT lane ...
FAIL d2_single got=32 want=41
FAIL inner_arity2_p0 got=129557927575568 want=101

$ bin/simple_seed test <scratch>/repro/enum_payload_subpattern_spec.spl
17 examples, 0 failures        # interpreter lane — correct, hence green
```

## Suggested fix order

1. `enum_pat_binding_syms` / `enum_pat_binding_positions`
   (`switch_operators_calls.spl:108-147`) — recurse into nested `Enum`/`Literal`
   sub-patterns, returning a path (slot chain) rather than a flat slot index.
2. `lower_enum_match` (`switch_operators_calls.spl:1356`) — emit a conjunction of
   discriminant tests along each path, with correct fallthrough to the next arm.
3. Until 1–2 land, make the failure **loud**: narrow `pattern_is_mir_native`
   (`expressions.spl:1396`) to return `false` for an `Enum` pattern whose payload
   contains a non-`Binding`/non-`Wildcard` sub-pattern, so those arms route to
   `flatten_enum_match_arm` and hit its existing `self.error`. A compile error is
   strictly better than a silent wrong value, and this step is small and local.

## Engine attribution correction (2026-08-01) — read before trusting the matrix above

The engine matrix's third column, "stage2 pure-Simple native (LLVM)", is
misattributed. `simple native-build --entry <f>` (and `--source ... --entry
...`) routes through `run_rt_native_build` -> the `rt_native_build` extern
(`src/app/cli/bootstrap_main.spl:112`), i.e. **the Rust seed's native
codegen embedded in the runtime**, regardless of which stage binary you
invoke. Proof: objects produced that way call `rt_enum_check_discriminant`,
a symbol emitted ONLY by `src/compiler_rust/**` codegen — `src/compiler/**`
has zero call-emission sites for it. That is why the "two compiled engines"
fail on an IDENTICAL shape set: they are the same codegen. No change under
`src/compiler/**` can affect that lane; its fix is Rust-side (seed
unbuildable on this host, ENOSPC).

The repo's ACTUAL pure-Simple MIR pipeline is reachable only via the
in-process driver (bare single `.spl` positional, no `--entry`), and at this
base:

- from a compiled stage2 it silently NO-OPS: `options.mode` does not survive
  the struct transport, `compile()` logs `[WARN] no mode matched, falling
  through` and returns Success with NO binary, exit 0 (fixed below);
- via the seed-interpreted driver (`simple_seed run
  src/app/cli/bootstrap_main.spl native-build <f> -o <o> --backend llvm`) it
  LOUD-FAILS nested payload sub-patterns (28 x `flatten_enum_match_arm`'s
  self.error on the verification matrix, phase-3 abort) — so on this one
  checked lane the defect was a hard error, not a silent wrong value.

## Fix (2026-08-01) — pure-Simple MIR lowering + in-process lane

Implemented at the MIR layer, where per-arm fallthrough already exists: each
arm's discriminant compare falls through to `next_block` on mismatch, and the
deep tests reuse exactly that target.

- `lower_enum_match` (`switch_operators_calls.spl`): an arm whose payload
  contains a nested `Enum`/`Literal` (per-arm `enum_deep_flags`, classified
  inline — a bool-returning helper's result read wrong through the call
  boundary on the seed-built stage2, the same recorded quirk that killed the
  earlier flatten attempt) is entered through a per-arm `ematch_deep` block
  chain emitted AFTER the outer discriminant compare passes; every failing
  sub-test branches to the arm's `next_block`, preserving arm-to-arm
  fallthrough. Arms with only Binding/Wildcard payloads keep the pre-existing
  single-compare emission unchanged.
- `emit_enum_payload_deep` / `emit_deep_subpattern` / `emit_deep_literal_test`
  (new): recursive payload walk. Nested variant tests via
  `rt_enum_discriminant` (an `rt_is_some` dual-ABI lane for nested `Option`),
  literal slot compares (int/bool raw word; text by content via
  `rt_text_eq_any`), nested binds installed from the extracted slot words
  (`rt_enum_payload` / `rt_tuple_get`, the same layout the flat bind path
  reads). Depth-1 Binding/Wildcard binds keep the pre-existing flat path
  (text retag, struct-name registration) untouched.
- `flatten_enum_match_arm` (`expressions.spl`): nested `Enum`/`Literal`
  sub-patterns now pass through UNCHANGED to MIR instead of being flattened
  into fresh always-matching bindings. Tuple/Struct flatten and the Range/Or
  loud error remain.
- `run_native_build_bootstrap` (`bootstrap_main.spl`): sets
  `options.cli_mode_text = "aot"` (same idiom as `_CliCompile/
  compile_targets.spl`), fixing the silent exit-0/no-binary no-op of the
  in-process native lane from a compiled stage2.

## Verification status — what is and is NOT proved

PROVED:
- The 28 loud phase-3 errors on the checked (interpreted-driver) lane are
  gone with the fix; the same matrix at base aborts with them. Reverting the
  two compiler files restores the errors.
- No regression on any working lane: the `--entry` (seed-codegen) lane
  produces byte-identical matrix output before/after; the 17-example spec
  stays green under `simple_seed test` (interpreter lane — lane-limited
  evidence by construction); stage2 rebuilds clean (728 compiled, 0 failed).

NOT PROVED — blocked by PRE-EXISTING pure-Simple-lane defects (all verified
present at base, on depth-1 controls the fix does not touch):
- printed-value correctness of the new lowering. The in-process LLVM lane
  currently miscompiles even `match 7: case 5/7` (`add void 7, 0` llc abort),
  drops enum construction payloads (`rt_enum_new` called with payload 0 for
  `Inner.A(41)`), and returns 0 from function calls (`d1_binding()` — a
  control correct on every other lane — reads 0), after which -O3 folds arm
  bodies away entirely. Until that lane is healed, no value-level assertion
  can pass on it for ANY enum code, fixed or not.

Nested `Range`/`Or` and depth>=2 `Tuple`/`Struct` sub-patterns remain
unsupported and are a loud `self.error`, never an always-match.
