# Backend divergence: `index_of` routes to a different runtime symbol under LLVM than under Cranelift/JIT

- Status: OPEN (P2)
- Status re-verified 2026-08-17 by source inspection (triage shard 02).
- **Filed:** 2026-07-28
- **Class:** wrong-answer (silent), backend divergence
- **Base revision:** origin/main `b410e53a7a2`
- **Affects:** `[T].index_of(v)` on an ARRAY receiver, LLVM/native backend only

## Summary

The same source compiles to different semantics depending on the codegen backend.

The Cranelift/JIT instruction emitter routes the `index_of` method name to
`rt_index_of`, which is receiver-polymorphic (tries `rt_array_index_of`, falls
back to `rt_string_find`). Both LLVM builtin-method tables instead route
`index_of` to `rt_string_find`, which is string-only and returns the -1
receiver-mismatch sentinel for an array receiver.

Consequence: `arr.index_of(x)` yields the correct index under Cranelift/JIT and
a constant -1 under LLVM — for every array receiver, whether or not the element
is present. Present-at-index-0 and absent are indistinguishable.

## Routing sites (emitted symbol, not method name)

Only two sites emit `rt_index_of`; grepping the method name `"index_of"`
returns four and conflates the two routings, which is what hid this.

| Backend | File:line | Emitted symbol | Receiver-gated? |
|---|---|---|---|
| Cranelift/JIT | `compiler/src/codegen/instr/calls.rs:3234` | `rt_index_of` | polymorphic at runtime |
| Cranelift/JIT | `compiler/src/codegen/instr/closures_structs.rs:1284` | `rt_index_of` | polymorphic at runtime |
| LLVM | `compiler/src/codegen/llvm/emitter.rs:191` | `rt_string_find` | NO — bare method name |
| LLVM | `compiler/src/codegen/llvm/functions.rs:2274` | `rt_string_find` | NO — bare method name |
| LLVM | `compiler/src/codegen/llvm/functions.rs:2611` | `rt_string_find` | yes, gated on `String\|string\|str\|text` — correct, leave alone |

`rt_index_of` is defined at `runtime/src/value/collections.rs:3051` and is
already declared to the LLVM backend: LLVM materialises externs from
`codegen::runtime_sffi::RUNTIME_FUNCS` (`llvm/backend_core.rs:1336`), and that
table carries `rt_index_of` at `runtime_sffi.rs:416` with signature
`[I64, I64] -> [I64]`, identical to `rt_string_find` at line 414. So retargeting
the two LLVM sites needs no new declaration and no ABI change.

## Why the MIR-level `index_of` special case does not save the LLVM path

`mir/lower/lowering_expr_method.rs:554` has an array-receiver `index_of` arm,
but it only BOXES the needle (BoxInt/BoxFloat) so `rt_value_eq` can compare it
against tag-boxed array elements. It does not redirect the call target. The
callee is still chosen later by the backend's bare-method-name table, so the
LLVM path still lands on `rt_string_find`.

## Scope check: is any other method divergent?

Mechanical diff of the Cranelift/JIT builtin tables against both LLVM tables,
resolving each `|`-alternation arm and honouring first-match-wins:

- `index_of` is the ONLY method whose emitted symbol differs between backends.

One adjacent defect found, NOT a divergence and NOT fixed here:
`llvm/functions.rs:2287` `"find" => rt_array_find` is unreachable, because line
2274 already matches `"find"`. The Cranelift/JIT tables map `"find"` to
`rt_string_find` as well, so `arr.find(..)` is uniformly wrong on both backends
rather than divergent. `rt_array_find` is dead code today. Filed as a note here;
fixing it changes behaviour on both backends and belongs in its own change.

Also noted, unchanged: `rt_string_index_of` (the only Option-returning
implementation) is unreachable by any method-name dispatch and is dead today.

## Reproduction

`scratchpad/idxof_ab.spl`:

```
fn main():
    val ai = [10, 20, 30]
    print("arr_i64_present_0 " + ai.index_of(10).to_string())
    print("arr_i64_absent " + ai.index_of(99).to_string())
    val at = ["aa", "bb", "cc"]
    print("arr_text_present_0 " + at.index_of("aa").to_string())
    val s = "hello world"
    print("text_present_6 " + s.index_of("world").to_string())
```

Run each side with an explicit backend on a compiler built `--features llvm`
(both levers hard-error when the feature is absent, so a successful run proves
which backend executed):

```
SIMPLE_BACKEND=cranelift <simple> idxof_ab.spl
SIMPLE_BACKEND=llvm      <simple> idxof_ab.spl
```

## A/B RESULTS

Compiler: built from `origin/main` `b410e53a7a2` with `--features llvm`
(LLVM 18). Identical source, identical compiler binary; the ONLY difference is
`--backend`. Commands:

```
<simple> compile idxof_ab.spl --native --backend=llvm      -o nat_llvm      && ./nat_llvm
<simple> compile idxof_ab.spl --native --backend=cranelift -o nat_cranelift && ./nat_cranelift
```

| Case | Expected | Cranelift native | LLVM native | JIT run path |
|---|---|---|---|---|
| `[10,20,30].index_of(10)` | 0 | **0** | **-1** WRONG | 0 |
| `[10,20,30].index_of(20)` | 1 | **1** | **-1** WRONG | 1 |
| `[10,20,30].index_of(30)` | 2 | **2** | **-1** WRONG | 2 |
| `[10,20,30].index_of(99)` | -1 | -1 | -1 | -1 |
| `["aa","bb","cc"].index_of("aa")` | 0 | **0** | **-1** WRONG | 0 |
| `["aa","bb","cc"].index_of("cc")` | 2 | **2** | **-1** WRONG | 2 |
| `["aa","bb","cc"].index_of("zz")` | -1 | -1 | -1 | -1 |
| `"hello world".index_of("hello")` | 0 | 0 | 0 | 0 |
| `"hello world".index_of("world")` | 6 | 6 | 6 | 6 |
| `"hello world".index_of("zzz")` | -1 | -1 | -1 | -1 |

PROVED. Every ARRAY receiver diverges: LLVM returns -1 unconditionally, so a
present element at index 0 is indistinguishable from an absent one. Every TEXT
receiver agrees across backends. Element type does not matter — `[i64]` and
`[text]` arrays both fail identically, which rules out the needle-boxing path
at `lowering_expr_method.rs:554` as the cause and confirms the callee choice is
the sole variable.

The JIT run path (`<simple> idxof_ab.spl`, run under `SIMPLE_JIT_STRICT=1`)
matched Cranelift exactly and emitted no `[jit-fallback]` marker, so the
correct-side result is genuine JIT codegen and not a silent demotion to the
interpreter.

### Post-fix re-run

With the two LLVM arms retargeted to `rt_index_of` and the compiler rebuilt,
all three paths agree and all are correct:

| Case | Expected | Cranelift native | LLVM native | JIT run path |
|---|---|---|---|---|
| `[10,20,30].index_of(10)` | 0 | 0 | **0** fixed | 0 |
| `[10,20,30].index_of(20)` | 1 | 1 | **1** fixed | 1 |
| `[10,20,30].index_of(30)` | 2 | 2 | **2** fixed | 2 |
| `[10,20,30].index_of(99)` | -1 | -1 | -1 | -1 |
| `["aa","bb","cc"].index_of("aa")` | 0 | 0 | **0** fixed | 0 |
| `["aa","bb","cc"].index_of("cc")` | 2 | 2 | **2** fixed | 2 |
| `["aa","bb","cc"].index_of("zz")` | -1 | -1 | -1 | -1 |
| `"hello world".index_of("hello")` | 0 | 0 | 0 | 0 |
| `"hello world".index_of("world")` | 6 | 6 | 6 | 6 |
| `"hello world".index_of("zzz")` | -1 | -1 | -1 | -1 |

Sibling-method regression check on `"abcabc"`, both backends, identical output:
`find_str`=1, `find`=1, `rfind`=4, `last_index_of`=4, `index_of`=1,
`index_of("zz")`=-1. Text routing is unchanged.

`index_of` keeps returning a raw `i64` with -1 for not-found and byte-based
offsets, matching `slice`/`len`. That is deliberate and unchanged by this fix.

## Fix

Split the `index_of` arm out of the two ungated LLVM arms and point it at the
receiver-polymorphic `rt_index_of`, so all backends agree:

- `llvm/emitter.rs:191` — `"index_of" => Some("rt_index_of")`, leaving
  `"find_str" => Some("rt_string_find")`.
- `llvm/functions.rs:2274` — `"index_of" => Some("rt_index_of")`, leaving
  `"find" | "find_str" => Some("rt_string_find")`.

`functions.rs:2611` is receiver-type-gated on text and stays as it is.

Do not delete the emission sites, and do not author a second `rt_index_of`: it
is the only receiver-polymorphic implementation, and removing it forces every
caller into a static array-vs-text choice.

## Verification note on binary provenance

The deployed `bin/simple` at the time of filing was built 2026-07-28 05:45,
while `5c75a1bbce0` (which added `rt_index_of` plus its registrations) landed
11:26 the same day. That binary contains no `rt_index_of`, no `[jit-fallback]`
marker and no `SIMPLE_JIT_STRICT` string, and is not linked against LLVM at all
(`SIMPLE_FORCE_LLVM=1` silently changed nothing because the feature was absent).
It therefore cannot demonstrate this divergence: on it BOTH backends route to
`rt_string_find` and every array `index_of` returns -1 identically. All A/B
evidence above comes from a compiler built from `origin/main` `b410e53a7a2`
with `--features llvm`.

## 2026-08-17 re-verification (lane s2_rust_codegen) — ALREADY FIXED, closing

Classified by CONTENT of current source, not by commit ancestry (SHA ancestry is
unsound in this repo — constant rebasing rewrites SHAs).

This doc's own `## Fix` section prescribes retargeting both LLVM emission sites
to the receiver-polymorphic `rt_index_of`. Both are present in current source:

- `src/compiler_rust/compiler/src/codegen/llvm/emitter.rs:356` —
  `"index_of" => Some("rt_index_of")`, with the surrounding comment block
  (lines 349-355) recording exactly why it must not go straight to the string
  symbol.
- `src/compiler_rust/compiler/src/codegen/llvm/functions.rs:2519` —
  `"index_of" => Some("rt_index_of")`.
- Regression assertion present at `emitter.rs:2368`:
  `assert_eq!(LlvmEmitter::runtime_method_name("index_of"), Some("rt_index_of"))`.

The callee is genuinely receiver-polymorphic —
`src/compiler_rust/runtime/src/value/collections.rs:5048`
`rt_index_of` tries `rt_array_index_of` first and falls back to `rt_string_find`
only when that returns `< 0`. So Cranelift and LLVM now emit the same symbol and
cannot diverge per backend.

Note for future triage: the worklist evidence line "no `rt_array_index_of`
emitted" was a mis-specified test. The chosen fix deliberately does NOT emit
`rt_array_index_of` from codegen — it emits `rt_index_of`, which calls it. Do not
reopen this row on a grep for `rt_array_index_of` in the backends.

Not proven here: no native LLVM execution was run this session; the evidence
above is source-level plus the existing in-crate unit assertion.

## Content re-verification 2026-08-17 (m2_rust_compiler lane) — ALREADY-FIXED

The triage evidence looked for `rt_array_index_of` being emitted; the landed fix
instead routes to a receiver-polymorphic `rt_index_of`, so the grep was a false negative.

- `src/compiler_rust/compiler/src/codegen/llvm/emitter.rs:349-356` — `"index_of" => Some("rt_index_of")`,
  with an explanatory comment naming this exact divergence ("Same source, two different answers per backend").
- `src/compiler_rust/compiler/src/codegen/llvm/functions.rs:2515-2519` — same mapping on the
  second LLVM emission path, comment records the old `rt_string_find` misrouting.
- `src/compiler_rust/compiler/src/codegen/runtime_sffi.rs:451-452` declares
  `rt_index_of` (`&[I64,I64] -> &[I64]`); `src/compiler_rust/runtime/src/value/collections.rs:5049`
  defines it, tag-dispatching to `rt_array_index_of` then `rt_string_find`.
- A unit assertion exists at `emitter.rs:2368`:
  `assert_eq!(LlvmEmitter::runtime_method_name("index_of"), Some("rt_index_of"))`.

Cranelift routes through the same `rt_index_of` tag dispatch
(`codegen/instr/closures_structs.rs:196`), so the two backends now agree.
