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
`cargo test -p simple-compiler --lib hir::` is 586 passed, 1 failed;
`implicit_generic_tests` 21/21, `conditional_empty_array_tests` 16/16. The one
failure is `calls::some_record_payload_tests::scalar_dynamic_and_array_payloads_keep_the_existing_erased_route`:
it expects `Some(value)` with `value: [i64]` to stay `any`, while the `Some`
arm that types an array payload as `Option<[i64]>` is release-line code
(6a2d359e87d); neither the test nor that arm is touched by this branch. It was
not run on the bare release tip.

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
