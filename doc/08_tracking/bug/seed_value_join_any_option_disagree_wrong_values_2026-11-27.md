# Seed value-join wrong values: ANY sibling, Option-wrapped, disagreeing arms (2026-11-27)

Follow-up to PR #12202 (weak empty `[]`/`{}` arms at the match/if join). Three
shapes still produced silent garbage on seeds m and r.
Section (A) is lane d29-c, (B) is lane d29-d, (C) is lane d29-e.

## (A) untyped/ANY sibling

Repro (seed r `simple-local-20261127r.exe` and older, JIT lane):

```simple
fn untyped(x):
    x
fn a2(xs: [f64]) -> f64:
    val r = untyped(xs)
    if r.len() > 0: r[0] + 0.25 else: -2.0     # printed 0.0, expected 1.75
```

Same through a join with a `[]` arm (`if c: [] else: untyped(xs)`, `match`
forms). Probes: rv3 `p_any` y1..y9, `q_s2`, `n3 s2`.

### Root cause

The seed erases an unannotated parameter, an unannotated return and every
generic parameter to `any` (`hir/lower/module_lowering/function.rs`,
`type_resolver.rs`). `untyped(xs)` was typed `any`, so `r`, `r[0]` and
`r[0] + 0.25` were tagged words. The if/match join then held a tagged word in
one arm and the raw `f64` `-2.0` in the other, and the consumer decoded both
the same way. `fn untyped<T>(x: T) -> T` failed identically:
`refine_generic_identity_return` instantiated the result for struct arguments
only.

### Semantics (owner decisions)

`any` is not a type of safe code; it is permitted only inside `unsafe:` and in
script mode. The seed does syntactic checks only: it does not infer types for
unannotated parameters (that belongs to the self-hosted compiler, with full
monomorphization as the target). Where an untyped value reaches a typed use in
safe code the seed reports it and asks for an annotation.

Rollout (owner decision, warn then error): the report is a WARNING by default
(`warning[uninferred-any]: <file>:<fn line>: in <fn>: ...`) and lowering
continues exactly as before, so existing untyped library code keeps building
and keeps its old run-time behaviour. `SIMPLE_STRICT_ANY=1` makes it an error.
S8-J flips the default to error once the listed families are typed.

### Fix (`hir/lower/implicit_generic.rs`)

1. The check (`LowerError::UninferredType`). Every site of a unit is printed
   once all bodies are lowered. Under `SIMPLE_STRICT_ANY=1` the lines are
   `error[uninferred-any]`, lowering fails with the first, and the error
   carries `SIMPLE_JIT_STRICT:` so the run lane cannot demote it to the
   interpreter. The seed's existing `SIMPLE_JIT_STRICT` switch is not reused:
   it governs JIT-to-interpreter fallback, a different rollout.
   An untyped value is an unannotated parameter, the result of a
   value-returning unannotated function, an unannotated local bound from one,
   or a method / field / operator result read out of one. It is reported as

   - an index receiver and a tuple index (`h.0`),
   - an operand of arithmetic, bitwise or ordered comparison,
   - an if/match arm joined with a typed arm,
   - a match subject.

   A call to an unannotated procedure (no value, or a unit-call tail) is `()`,
   not an untyped value; a callee declared further down is judged once every
   body is lowered.

2. Call-site instantiation of the `T -> T` signature shape only (no inference
   inside bodies): the existing `refine_generic_identity_return` hook now
   instantiates for every concrete argument type instead of structs only, and
   also covers the unannotated spelling `fn f(.., x, ..): x`. One type variable
   takes one type (`pick<T>(a: T, b: T)` needs agreeing arguments); no `[any]`;
   `bool`/`char` stay tagged. The erased callee returns a tagged word, so a
   numeric result is decoded with a cast. This is kept because the explicit
   generic is the form the owner rule points users to, and it printed the same
   garbage on r.

3. Script mode in the seed is the entry file kind only: `.shs` / `.sscript`
   are scripts, `.spl` is compiled mode, spec files included. Imported modules
   of a script are not script code. The rest of the owner's precedence
   (`@source_mode(...)` header > `--source-mode` > `simple.sdn [source_mode]`
   > file kind) is not read by the seed. An earlier revision also treated a
   `.spl` entry with top-level statements and no `main` as a script; that
   heuristic is dropped.

### Known gaps

- Not rejected: an untyped value passed on untouched, used as a condition,
  compared with `==`/`!=`, or iterated with `for`.
- Explicit `any` and explicit generic bodies are untouched (`fn f(x: any)`,
  `fn first<T>(xs: [T]) -> T`): a join of such an arm with a raw scalar is still
  the garbage shape. The existing staged "`Any` outside `unsafe:`" warning owns
  those.
- A callee compiled in another unit (per-module native-build) is never judged;
  only calls whose callee body is lowered in the same unit are.
- The `<seed> test` lane interprets and never lowers HIR, so it neither
  enforces nor exercises any of this.
- A function-tail join is not reported: `fn f(c: bool, xs: [f64]) -> [f64]:
  if c: xs else: opaque(xs)` lowers its tail `if` as a statement, so the
  join check never sees the two arms.
- The reported location is the declaration line of the enclosing function,
  not the line of the use (`Expr` nodes carry no span in the seed).

### Reported source (errors under `SIMPLE_STRICT_ANY=1`)

Per-family site list with `file:line` for migration lanes:
`uninferred_any_sites.md` in the session scratchpad (handed to the
coordinator; not tracked).

Census: seed lowering of each of the 162 `src/` files that declare an
unannotated parameter (146 lib, 9 app, 7 compiler), one unit per file, all sites
reported. 20 units stop on an unrelated error first and are not classified;
files whose only untyped surface is an unannotated *return* are not in the list.

Fixed with real types:

- `src/lib/nogc_sync_mut/spec.spl` `to_be_close_to(expected, tolerance)` ->
  `f64, f64` (trait `ExpectScalarMatcher`, its `i64` impl, `ExpectHelper`);
  loaded by every spec.
- `src/lib/common/complex/{arithmetic,exponential,trigonometric,types,utilities}.spl`:
  complex numbers are `(f64, f64)`; 5 units, 121 site lines. Same output on r
  and u before/after for an add/multiply/divide/polar/power/sqrt probe.
- `src/lib/nogc_sync_mut/tls/_TlsUtilities/{text_ops,hex_encoding}.spl`:
  `xor`/`or` are `(i64, i64) -> i64`; `index`/`length` parameters are `i64`.

Reported and NOT fixed: 603 sites in 34 directories (deduplicated by
function, value and kind of use; same numbers as the site list). They are
tuple-as-record or heterogeneous-array code whose parameter is the whole
untyped record, so each needs the record's type written down (a struct or a
full tuple type), not a one-word annotation:

| family | sites |
|---|---|
| `src/lib/nogc_async_immut/persistent_sorted_map` | 59 |
| `src/lib/nogc_sync_mut/compression` | 43 |
| `src/lib/gc_async_mut/cache` | 39 |
| `src/lib/nogc_sync_mut/cache` | 39 |
| `src/lib/nogc_async_immut/persistent_map` | 36 |
| `src/lib/nogc_async_immut/persistent_vec` | 36 |
| `src/lib/nogc_async_immut/combinators` | 34 |
| `src/lib/gc_async_mut/mqtt` | 33 |
| `src/lib/nogc_async_mut/mqtt` | 33 |
| `src/lib/nogc_sync_mut/mqtt` | 33 |
| `src/lib/gc_async_mut/oauth` | 32 |
| `src/lib/nogc_async_mut/oauth` | 32 |
| `src/lib/nogc_sync_mut/oauth` | 32 |
| `src/lib/nogc_async_mut/dns` | 20 |
| `src/lib/nogc_sync_mut/dns` | 20 |
| `src/lib/gc_async_mut/benchmark` | 12 |
| `src/lib/nogc_async_immut/persistent_trie` | 12 |
| `src/lib/nogc_async_mut/benchmark` | 12 |
| `src/lib/nogc_sync_mut/benchmark` | 12 |
| `src/lib/nogc_sync_mut/tls` | 12 |
| `src/compiler/15.blocks` | 4 |
| `src/lib/nogc_async_mut/cache` | 4 |
| `src/lib/nogc_async_mut` | 2 |
| `src/lib/nogc_sync_mut/src` | 2 |
| `src/app/mcp` | 1 |
| `src/lib/gc_async_mut/src` | 1 |
| `src/lib/nogc_async_immut/persistent_list` | 1 |
| `src/lib/nogc_async_immut/persistent_set` | 1 |
| `src/lib/nogc_async_mut/linalg` | 1 |
| `src/lib/nogc_async_mut/llm` | 1 |
| `src/lib/nogc_async_mut/mcp` | 1 |
| `src/lib/nogc_async_mut/src` | 1 |
| `src/lib/nogc_sync_mut` | 1 |
| `src/lib/nogc_sync_mut/io` | 1 |

With the default warning these units build and run as before: `run
test/01_unit/lib/immut/persistent_map_spec.spl` is 64 passed with 17
`warning[uninferred-any]` lines. Under `SIMPLE_STRICT_ANY=1` the same run
fails at `hamt_node_tag`. `<seed> test` interprets and prints nothing.

### Tests

`hir/lower/tests/implicit_generic_tests.rs` (21 tests; they fail without the
fix; the rule is exercised with `set_strict_any(true)`, the default with one
warning-mode test, and the full report list through
`take_uninferred_any_reports`). On the tree rebased over #12253:
`cargo test -p simple-compiler --lib hir::` is 588 passed, 0 failed;
`implicit_generic_tests` 21/21, `conditional_empty_array_tests` 16/16.
`calls::some_record_payload_tests::scalar_dynamic_and_array_payloads_keep_the_existing_erased_route`
failed on the bare release tip (3e63398dd11) since #12253 types
`Some(<array with a declared type>)` as `Option<[T]>`; it is split here into the
scalar/dynamic erased-route test and an `Option<[i64]>` test.

### Review fixes (Fable review of 9f740e8287c)

- A local callable (lambda, fn-typed parameter) named like an identity-shaped
  function was instantiated as that function (`val id = \v: "n={v}"; id(n)`
  typed `i64`). Only a callee that lowered to a global is instantiated, looked
  up by its resolved symbol and never by the bare name.
- `uninferred_locals` kept the entries of lambda-local slots after the lambda
  truncated the local table, so annotated locals that reused the slots were
  reported. The entries are pruned with the truncate.

### Verification (seed `simple-local-20261128d.exe`, sources `8bfe7aae531`, vs seed r)

Default (warning) mode. Probes: 70 identical outputs out of 92 (`rv3/{a,b,c}`,
`mt`, `mt2`, `kinds`, `dv`); nothing correct on r changed. Every difference:

- garbage on r, correct now, from this section: `p_any` y1..y9
  (`y1 -2.0 1.75` ... `y9 1.75 -2.0`), `q_s2`, `n3 s2` (b and mt2 copies),
  `n4 c0`; class field read and `u64` through the identity in unannotated /
  explicit-generic / forward-declared form (`kinds/ke,kf,ki`);
  `pick<T>(a: T, b: T)` on `u64` and `[f64]` (`dv/pick`, `dv/p5`).
- garbage on r, correct now, from the rebased (B) fix #12253: `q_s5`, `n3 s5`
  (b and mt2 copies), `p_opt`.
- timeout on r, correct now: `mt2/h1400`, `h3000`, `long`, `long1500` (the
  rebased #12235 long-match-chain fix).
- `n1`, `kinds/ka`: one line each prints a raw word that differs between any
  two runs (explicit `any`, unchanged).

Still garbage, now with a `warning[uninferred-any]` naming the function, and an
error under `SIMPLE_STRICT_ANY=1`: `n4 c1` (`untyped([])` joined with
`untyped(xs)`), `dv/d1` (method result), `d3` (tuple index), `d5` (join), `d7`
(match subject) of an untyped value. `dv/d6` (`fn g(h): h.1 + 0.25`) stays
correct and warns.

Review probes (`rev_d29c`, 23 files): same output on r and the new seed, no
engine demotion; `t5`/`t5b` differ only in a raw word that differs between any
two runs. `t9`/`k3` (annotated locals after a lambda) print no warning;
`k1`/`k2`/`t7`/`xm/main3` (local callable shadowing an identity function)
print `n=5`.

`run test/01_unit/lib/immut/persistent_map_spec.spl`: 64 examples, 0 failures,
17 warnings. `<seed> test` of `parsers_json_core_spec` (101/101),
`storage_view_v1_spec` (34/34) and `persistent_map_spec` (64/64) pass.

Measured on earlier builds of this branch and not re-run on this seed:

- Dropping the top-level-statement script heuristic (seed 20261128a): `<seed>
  run` over 60 sampled specs, r vs that seed, 58 identical exit codes; the 2
  that differ are 90 s timeout flaps in both directions (`manual_mode_spec`
  re-run to completion: rc=1 on both).
- `<seed> test` over 252 specs (seed u, error-by-default): identical verdicts
  to r.
- Rust native-build of `bootstrap_main.spl` (seed u, error-by-default): 752 of
  1685 closure objects, no report and no failed file, before a 50-minute cap.

## (B) Option-wrapped weak-empty arms

Repro (seed r, `simple-local-20261127r.exe`): `val r = if c: Some([]) else: Some(xs)`
(or the `match` form) with `xs: [f64]`, then `match r: case Some(v): v[0] + 0.25`
returned `0.0` for BOTH arms (expected `-2.0`/`1.75` with a `len() > 0` guard).

Root cause, two parts in `src/compiler_rust/compiler/src/hir/lower/expr/`:

1. `calls.rs`: `Some(x)` only kept a typed `Option<T>` for Function/Struct
   payloads; an array/dict payload was erased to `ANY`, so the join type and the
   `v` binding were `ANY` and `v[0]` was a dynamic index over raw f64 storage
   (garbage). This also broke the non-empty `Some(ys)` vs `Some(xs)` join and a
   plain `val r = Some(xs); match r:` read.
2. `control.rs`: the PR #12202 weak-empty rule (`weak_expr`, `same_collection_kind`,
   `ast_expr_tail_is_array_repeat`) did not look through `Some(...)`, so even once
   typed, `Some([])` (`Option<[i32]>`) won the join over `Some(xs)`.

Fix: `Some(<array|dict>)` now types as `Option<payload>`; `weak_expr` treats
`Some(e)` as `e`; `same_collection_kind` compares Option payloads;
`ast_expr_tail_is_array_repeat` sees through `Some(..)` so `Some([x; 0])` is never
weak. Tests: `hir/lower/tests/conditional_empty_array_tests.rs`
(`option_wrapped_*`).

Not covered here (siblings): `if c: Some(xs) else: None` / `None` first, and
other Any-typed payload reads.

Verification (seed r vs v = r + this fix; 77 probes from rv3 a/b/c + mt/mt2): 6
probe files differ. Fixed: `p_opt` o1/o2 (`0.0 0.0` -> `-2.0 1.75` / `1.75 -2.0`),
`q_s5` and the `n3` tail lines (`0.0 0.0` -> `-2.0 1.75`). The remaining diffs
(`n1` line 24, `n3` line 4, `q_s2` line 2, `p_any` y3/y4/y7) are garbage values on
BOTH seeds (differ run to run: uninitialised/address-like reads) and stay wrong
(sibling lanes). No probe that was correct on r changed on v. Specs on v:
storage_view_v1 34/34, parsers_json_core 101/101, match_empty_array_bug 10/10.

### (B) revision after review (c41c12ff143 blocked)

The first fix typed `Some([])` as `Option<[i32;0]>` (the empty-array default became
authoritative), so an untyped `Some([])` later replaced or filled read garbage (probes
rvd a02/a03/a18/b02/b03/b05/c04). Revised: `Some(<weak empty literal>)` is NOT typed
(it keeps the pre-existing erased type, exactly as before the change; `Some([x; 0])`
still types), only `Some(<concrete array|dict>)` becomes `Option<T>`. The join treats
the erased weak `Some([])` as weak and adopts the concrete sibling's Option type
(`same_collection_kind` now looks through Option only, never Result).
`hir_types_compatible` admits pointer-form `T?` vs `Option<T>` (no more "declared
return type mismatch admitted" for `-> [T]?`). Dict sibling (a15) uses the same path.
Tests: `some_empty_array_stays_weak_when_later_replaced_or_filled`,
`option_wrapped_empty_dict_defers_and_option_never_adopts_result`.

Second revision: `Some(<array/dict literal>)` also stays erased (a literal's element type is
a guess: `var c = Some([0]); c = Some([1.5, 2.5])` and heterogeneous `Some([..])` pushes read
garbage when typed, rvd b03/b05). Only `Some(<local|call|field>)` with a declared array/dict
type becomes `Option<T>`.

### (B) review follow-ups (2026-11-28)

- Kind fix: the erased `Some([])` / `Some({})` arm used to adopt any sibling Option (d10 k2:
  `if c: Some([]) else: Some(base_dict)` then `d.len()` = -1 on y JIT). The array-vs-dict kind
  is now derived from the weak arm's literal (`weak_literal_is_dict`, peeling `Some`) at both
  join sites (if and match) and must equal the sibling Option payload's kind. Test:
  `option_wrapped_empty_literal_never_adopts_sibling_of_other_collection_kind`.
- OPEN (owner no-ANY rule): untyped `Some(<literal>)` is still the erased ANY interim.
  Proper fix: a deferred element type `Option<[?E]>` resolved from the expected type, the join
  sibling, or the first push; defaulted at function end; conflicting evidence = compile error.
- Still wrong, to be solved by that fix: rvd/y d04 j6 (well-typed
  `if c: Some([7.5]) else: Some(xs)` = 0.0 on r and y); d07/d14/d08/d10 k5 (ill-typed literal
  reassign/push is silent garbage, should be errors); d13 (`-> [i64]?` returning `Some([f64])`
  should be a hard error).

## (C) disagreeing siblings

### Symptom (seed `r` and older)

```simple
val r = if c: 1 else: "a"          # "{r}" for the else arm: 6225353883777
val r = if c: 1.5 else: 2          # the int arm read as f64 bits: 0.000...277
val r = match k:                   # probe p_kind k6
    case K.A: {}
    case _: 5                      # "{r}": <value:0x5>
val r = match k:                   # probe n1 d1 / d2
    case K.A: []
    case K.B: xs                   # [f64]
    case K.C: ys                   # [i64]: r[0] printed 0.000...277 or 6090532272433
```

No diagnostic, exit 0. The seed type checker does not catch it either:
`type/src/checker_infer.rs` (`Expr::If`) discards the `unify` result of the two
branch types, and `Expr::Match` answers a fresh type variable.

### Semantics (owner rule: no ANY in safe code)

The join of two value arms is typed. `ANY` / `[ANY]` is never produced.

1. **int vs float joins to the float type.** This is the one implicit
   conversion the language already has (mixed arithmetic promotes to float;
   int -> float widening at declared slots stays implicit, float -> int is
   error E1003). The int arm is wrapped in a real `Cast` to the float arm's
   type, so the value is converted, not reinterpreted. The promoted (float)
   join never reaches an integer slot silently: stored into an annotated int
   binding (`val r: i64 = if c: 1 else: 2.5`), an int assignment target, an int
   struct field, an int parameter or return, or used as an index, it is
   `error[E1003] ... is declared as `i64` but receives `f64``. Review found the
   first cut of this fix dropped that check and turned `21 42` into `0 0`.
2. **Any other disagreement is a compile-time type error in safe code**,
   reported with the existing lowering type-error tag `error[E1003]`, which the
   run lane never demotes to the interpreter (`jit_failure_must_propagate`).
   Judged classes: `bool`, int, float, `text`, array, dict. Two arms disagree
   when their classes differ (`1` vs `"a"`, `{}` vs `5`, `[]` vs `"txt"`,
   `[]` vs a dict) or when both are concrete arrays whose element types
   disagree, recursively (`[f64]` vs `[i64]`, `[i64]` vs `[text]`). There is no
   array promotion: `[i64]` does not become `[f64]`. An array literal that holds
   only empty literals (`[[]]`, `[[], []]`) is weak below that nesting depth,
   like `[]` itself: `if c: [[]] else: xs` with `xs: [[f64]]` is accepted.
3. **Declared expected types do not relax the rule.** A union annotation
   (`val r: i64 | text = if c: 1 else: "a"`) printed `<enum@0x...>` on seed `r`:
   the seed has no typed union join, so the same error is reported. The fix for
   the user is one arm type (explicit conversion) or an enum wrapping the
   alternatives. A union-typed join is a named gap, not implemented here.
4. **Permissive contexts**, both detected at HIR lowering:
   - `unsafe:` blocks (`ctx.unsafe_depth > 0`) keep the untyped first-arm join.
   - Script mode, by FILE KIND (owner decision 2026-11-27): a `.shs` or
     `.sscript` entry file is a script; a `.spl` file is a compiled safe module,
     spec files (`*_spec.spl`) included. The driver sets
     `hir::set_entry_script_mode` for the lowering (`run_file_jit_outcome` in
     `driver/src/exec_core.rs`), and only functions OWNED BY THE ENTRY FILE
     (`current_function_owner == None`) are exempt; modules a script imports
     are still checked. This file-kind test is TEMPORARY: the owner precedence
     is file-header `@source_mode(...)` > CLI `--source-mode` > `simple.sdn
     [source_mode]` > file kind, and plan lanes S4-A / S4-B replace this check
     with that resolution. None of the three overrides is read here yet. (The
     first cut used a heuristic -- top-level statements or no `main` -- which
     exempted every spec file; it is gone.)
   The native-build lane never sets script mode: it has no interpreter to give
   a mixed join dynamic semantics, so the rule is unconditional there.

Left to the existing rules (not judged): bottom arms (`nil`, `panic`, `return`),
arms whose block ends in a statement (`continue`, `break`, an assignment, a
statement-form `if`), a weak empty `[]` / `{}` against the same collection
kind, statement-form `match` (value discarded), and every type whose seed
typing is not authoritative: ANY, struct, enum, Option, tuple, char, and return
types borrowed by the untyped-receiver method search
(`suffix_guessed_return_types`).

### Message

```
error[E1003] type mismatch: value arms disagree in `d1` (fn at line 65): the arm at
line 68 is `[f64]` but the arm(s) from line 69 is `[i64]`; give every arm one type
(convert explicitly, or wrap the alternatives in an enum) -- only `unsafe` code or a
script may mix arm types
```

`Expr::If` carries no span, so an `if` is located by its function and that
function's declaration line plus `the then-arm` / `the else-arm`; a `match`
also names the arm lines. A function of an imported module is named with its
module path.

### Known limits

- A block-form `if` whose arm is a statement block ending in a statement
  `if` / `match` (e.g. `val r = if c:` + indented `match` + `else: "txt"`) is not
  judged: that arm's value comes from the tail-statement join
  (`hir_tail_if_value_type`), a separate path.
- A function's implicit tail (`fn t(c: bool) -> text: if c: 1 else: "a"`, or a
  tail `match`) is not a join error. It was and still is the untagged
  `declared return type mismatch`, which drops the module to the interpreter
  with a `[jit-fallback]` line and prints the right values (same on `r`, `w`).
- Where the int -> float conversion lands in existing `src` code was not
  counted; the sweeps only looked for errors.
- The int-slot check covers a join used DIRECTLY as the stored value. A float
  join bound to an untyped local and later copied into an int slot
  (`val r = if c: n else: 2.5` then `val q: i64 = r`) is the general
  float-into-int-binding hole, which exists without any join and is not closed
  here; only the index use of such a local is rejected.
- An explicit empty repeat `[0; 0]` lowers to an empty array literal and is
  treated as weak; `[0; 0]` vs `[f64]` keeps the pre-existing behaviour.
- Dict key/value disagreement between two concrete dicts is not judged.
- Sources routed straight to the interpreter (`SIMPLE_EXECUTION_MODE=interpreter`,
  the forced-interpreter allowlist) are never lowered, so nothing is reported
  there; this is the pre-existing limit of every lowering type error.
- `type/src/checker_infer.rs` is unchanged. Its `if` unification result is still
  discarded; the lowering is the enforcing site because it owns the join type
  and the unsafe / script context.

### Behaviour change to expect

Programs that printed the right text on seed `r` for the inputs tried are now
rejected, because the other arm of the same join was read as garbage or only
worked by accident:

- `[]` vs a dict or text (`r.len()`, `"{r}"` happened to work), `[1]` vs `[1.5]`
  and `[1]` vs `["a"]` printed whole (element reads were wrong).
- An int/float join in an int slot: `val r: i64 = match k: case 0: n; case 1:
  n * 2; case _: 0.0` printed `21 42` on `r` for the int arms and garbage for
  the float arm. It is now `binding `r` is declared as `i64` but receives
  `f64``; likewise `r = if c: 1 else: 2.5` (int `r`), `P(n: if c: k else: 2.5)`
  and `xs[r]` with `r` a float.
- A `.spl` file with top-level statements or no `main` is no longer exempt: it
  is a compiled module by file kind, so its own mixed joins are rejected.

### Fixed in `src`

- `src/lib/gc_async_mut/pure/nn/embedding.spl` (two copies of the lookup loop):
  the row index read from an `[f64]` tensor was used as an array index and
  pushed into `last_indices: [i64]` unconverted; the comment said "convert from
  f64 to i64" but the code was `val idx_int = idx`. Now `idx as i64`, and the
  bounds test compares against `0`. Found by the float-index error through
  `test/01_unit/lib/gc_async_mut/embedding_spec.spl`.

### Residuals found in review (NOT fixed here)

The first two behave the same on `r` and on the fixed seed.

- Integer width mixes are not judged and are misread: `val r = if c: n else: m`
  with `n: i32`, `m: i64` returns `1705032704` for `m = 6000000000` (the join
  takes the first arm's width). Same for `u8` vs `i64`. All ints are one join
  class here; a width rule (widen to the larger, or E1003) is open.
- A 3-arm implicit tail `match` in a `-> f64` function with arms `1` / `2.5` /
  `3` returns `0.0` for every arm. The 2-arm form and the tail `if` form are
  right. The tail-statement join (`hir_tail_if_value_type`) is a separate path
  from the value join fixed here.
- A lambda body is value position even when the call result is discarded:
  `val f = z if c: p(1) else: q(2)` followed by `f(true)` is now E1003
  (`i64` vs `text`); it ran on `r`. The lowering cannot see that every call
  site discards the result. Write the lambda with a statement body, or give
  both arms one type.
- Arms typed through a generic call or an untyped lambda (`gen(x)`, `y: y +
  1`) are ANY and belong to class (A); they still print garbage.

### Sweep of existing code (2026-11-27)

Run with an audit build of the same rule that printed every site instead of
stopping at the first. Newly rejected sites in `src/`: **none**.

| lane | input | lowered to completion | not verified | value-join sites |
|---|---|---|---|---|
| run/JIT, flattened import closure | 1,351 unit specs (first 2 per directory of `test/01_unit/lib` and `test/01_unit/compiler`, plus the 4 named specs) | 1,229 | 122 (99 stopped on an unrelated HIR error, 2 MIR, 3 module load, 18 no verdict) | 0 |
| `compile`, per file | 7,453 files: all of `src/compiler`, every 3rd `src/lib`, about every 4th `src/app`, every 6th `src/os` | 5,958 | 1,495 hit the 15 s cap on a loaded host (1,169 of them in `src/compiler`) | 0 |
| `compile` on the final seed, 400 s cap | 22 of those capped `src/compiler` files, one per layer directory | 16 | 6 failed on unrelated semantic errors | 0 |

The audit found one false positive, fixed in the rule before the final build:
`src/compiler/00.common/data/data_schema_resolver.spl:294,299`, a `match` arm
that ends in `continue` and so yields no value. Not run: the full bootstrap and
the rest of `test/01_unit` (9,985 specs; a spec takes 30-200 s through
`simple test` here). `storage_view_v1_spec`, `parsers_json_core_spec`,
`if_val_match_diverging_value_type_spec` and `match_empty_array_bug_spec` pass
through `simple test` on the final seed.

#### After the review fixes (2026-11-28, seed `z`)

Spec files are now compiled modules, so their own functions are checked too,
and the int-slot and float-index errors are new. Re-run in the final
(non-audit) mode, which stops at the first error of a unit:

| lane | input | lowered to completion | not verified | new E1003 |
|---|---|---|---|---|
| run/JIT, flattened import closure | the same 1,351 unit specs | 1,232 | 119 (100 stopped on a HIR error, 3 MIR, 3 module load, 13 no verdict) | 1: the float index in `embedding.spl` (fixed above); no value-join rejection |
| `compile`, per file, 15 s cap | first 1,507 files of `src/compiler` (stopped there: about 35 files a minute on the loaded host) | 889 | 618 capped; `src/lib`, `src/app`, `src/os` not re-run | 0 |

Both sweeps ran on the first `z` build, before the match-chain hollow-literal
relaxation and the rebase onto #12253; the probe sets and the five specs were
re-run on the final build.

So the file-kind switch rejected no spec in the sample, and it was kept. The
int-slot and float-index rules were NOT swept over `src/lib`, `src/app` or
`src/os` per file; they are covered only as far as the 1,232 spec closures
reach. The five specs (the four above plus `embedding_spec`) pass through
`simple test` on the fixed seed.

### Tests

`src/compiler_rust/compiler/src/hir/lower/tests/conditional_empty_array_tests.rs`:
`disagreeing_value_arms_are_a_type_error_in_safe_code`,
`disagreeing_match_arms_name_both_types_and_arm_lines`,
`int_and_float_arms_join_to_float_by_converting_the_int_arm`,
`value_join_rule_leaves_agreeing_bottom_weak_unsafe_and_statement_forms_alone`,
`script_entry_functions_keep_the_untyped_join_and_compiled_entries_do_not`.
`promoted_float_join_never_reaches_an_int_slot`,
`nested_empty_literals_are_weak_at_every_depth`.
One older pin was removed because it now is the error (`[1]` vs `[text]`), and
the `[]` vs dict pin moved inside `unsafe:`. The `["typed"; 0]` vs `[1]` pin is
kept: an explicit empty repeat is a weak arm, so that join still lowers.
