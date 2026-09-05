# src/app/interpreter/async_runtime/generators.spl fails to parse

Status: CLOSED (not reproducible)
Status re-verified 2026-08-17 by source inspection (triage shard 01).

- **File**: `src/app/interpreter/async_runtime/generators.spl`
- **Found during**: fixing `generator_intensive_spec.spl` to stop shadowing
  the real `GeneratorState` enum (see
  `doc/08_tracking/bug/generator_intensive_spec_shadows_generatorstate_variants_2026-08-10.md`).

## What's wrong

The module cannot be parsed by the current self-hosted compiler, so it
cannot be `use`d from anywhere, including a test spec. Two independent
parse blockers were found:

1. **Reserved keyword as parameter name.** Every `Generator`-consuming
   function used `gen` as a parameter name (`fn generator_next(interp:
   &Interpreter, gen: &mut Generator) -> ...`). `gen` is a reserved keyword
   in Simple (see `.claude/rules/language.md`). **Fixed in this pass** —
   all occurrences renamed `gen` -> `g` (module is not imported/called from
   anywhere else in the tree, confirmed via
   `grep -rn "async_runtime" src/app/interpreter/*.spl` returning nothing,
   so the rename is safe and self-contained).

2. ~~**Struct-style enum-variant patterns/literals not accepted by the
   current grammar**~~ — **THIS DIAGNOSIS WAS WRONG.** Bisected 2026-08-10
   by truncation against the seed binary
   (`bin/release/x86_64-unknown-linux-gnu/simple`, mtime 2026-08-10
   11:06:25). Every construct blamed below parses FINE:
   - `Suspended { next_value: Value, env: Environment }` (decl, :12) — OK
   - `GeneratorState.Suspended { ... }` (construction, :85, :111) — OK
   - `case GeneratorState.Suspended (next_value, env ):` (:96) — OK
   - `&Interpreter`, `&mut Generator`, `Box<Block>`, `Array<Value>`,
     `usize`, `&*g.body` — all OK

   **The actual and ONLY blocker was `generators.spl:130`:**
   `callback: Fn(Value) -> Result<(), InterpreterError>`.
   Simple's function-type syntax is `(Args) -> Ret`
   (cf. `callback: (JsValue) -> JsValue`, `closure: () -> i64`,
   `type Handler = fn(Event) -> ()`). Capital `Fn(...)` is Rust's `Fn`
   trait — a **Rust-ism, i.e. INVALID SOURCE, not a parser gap**. Fixed in
   `.spl`; the parser was correctly rejecting it and was NOT changed.

   Sibling census (`Fn(` in owned source) found exactly 2 sites, both in
   this same never-imported draft package: `generators.spl:130` and
   `actors.spl:30`/`:33`. Both fixed.

   Original (now-superseded) symptom:

   ```
   error: parse: Cannot parse module ".../generators.spl": Unexpected
   token: expected comma or newline, found LParen
   ```

   Reproduce:
   ```
   bin/simple test <any spec containing:
     use app.interpreter.async_runtime.generators.GeneratorState>
   ```

   The likely culprits (not yet bisected past the first failure) are the
   Rust-flavored constructs throughout the file:
   - struct-style variant construction: `GeneratorState.Suspended {
     next_value: value.clone(), env: interp.env.clone() }`
   - a positional destructure of a struct variant with a stray space
     before the paren: `case GeneratorState.Suspended (next_value, env ):`
   - reference/generic types used throughout: `&Interpreter`, `&mut
     Generator`, `Box<Block>`, `Array<Value>`, `Fn(Value) ->
     Result<(), InterpreterError>`, `usize`

   Nothing in the tree currently imports this module (see grep above), so
   this has been sitting unreachable/unverified — likely an early draft
   that was never brought into the working grammar, matching the
   "iso-ownership pipeline works but unreachable" pattern already seen
   elsewhere in the interpreter.

## Impact

`generator_intensive_spec.spl` cannot import the real `GeneratorState`/
`Generator` types from this module until it parses. The spec fix instead
locally re-declares an enum with the SAME variant names and payload shapes
(`Created`, `Suspended(next_value, env)`, `Running`, `Completed`) as a
documented mirror, with `env` stood in as a placeholder `i64` (the real
type is `Environment`, unavailable here because the defining module does
not parse). This is called out at the top of the enum block in the spec.

## Unblock condition

Rewrite the struct-variant construction/pattern sites and reference/generic
type annotations in `src/app/interpreter/async_runtime/generators.spl` to
match the grammar this compiler actually accepts (see any working enum
with payload fields elsewhere in `src/app/interpreter/` for the accepted
shape), then re-point `generator_intensive_spec.spl` at a real `use`
import instead of the local mirror enum.

## Resolution 2026-08-10

`generators.spl` **now parses** and `GeneratorState` is importable and
constructible. Verified by import, not merely by parse — a probe doing
`use app.interpreter.async_runtime.generators.GeneratorState` constructed
and pattern-matched all **four** variants (the enum has NO `Yielded`
variant):

- `Created`, `Running`, `Completed` — constructed + matched
- `Suspended(next_value: 42, env: 0)` — constructed, destructured, `v=42 e=0`

Fixes applied, all in `.spl` (invalid source), parser untouched:
- `generators.spl:130` `Fn(Value) ->` -> `(Value) ->`
- `actors.spl:30,:33` `Fn(Message) ->` -> `(Message) ->`
- `futures.spl:62` `if value Some(result)` -> `if val Some(result)`

## Status: PARTIALLY RESOLVED — generators.spl FIXED; package import still blocked

The spec still cannot drop its local mirror. `use ...generators.GeneratorState`
loads the package `__init__.spl`, which eagerly imports **`actors.spl`**, an
unmigrated Rust draft that does not parse. Remaining blockers there, found by
iterative bisect and deliberately NOT half-migrated (reverted to avoid leaving
a partially-rewritten module):

- `actors.spl:53` `static mut NEXT_ACTOR_ID: u64 = 0`
- `actors.spl:56` `static mut ACTOR_REGISTRY: Dict<u64, Actor> = {}`
- `actors.spl:60,66,72,94,105` Rust `unsafe { ... }` blocks
- `actors.spl:59` etc. reserved keyword `actor` used as a parameter/binding
  name (same class as the original `gen` issue; note `bin/simple run` does
  NOT enforce this, only `bin/simple test` does)

`static mut` and `unsafe { }` have no Simple equivalent, so unblocking
requires redesigning this module's global-actor-registry state — an
unbounded rewrite of a draft that nothing in the tree imports and whose
semantics are unverifiable (no test exercises it). Filed rather than
guessed at.

**Unblock condition:** migrate `actors.spl` off `static mut`/`unsafe`/`actor`
-as-identifier, then re-point `generator_intensive_spec.spl` at the real
`use` import and delete its mirror enum.
