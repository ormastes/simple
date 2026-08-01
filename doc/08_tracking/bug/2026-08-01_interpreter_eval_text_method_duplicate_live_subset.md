# eval_text_method is defined twice; the LIVE copy is a strict subset

**Date:** 2026-08-01
**Status:** FIXED (live copy completed; duplicate removed)
**Filed by:** follow-up from commit `113f0864c7a`
**Area:** pure-Simple interpreter, text builtin method dispatch

## Symptom

`text` methods `byte_at`, `slice`, `char_at`, `parse_int`, `to_upper`,
`to_lower`, `to_string`, `find`, `find_str`, `rfind`, `last_index_of` were
**silently unsupported** in the pure-Simple interpreter. They did not raise a
visible error at the call site — the arm fell through to
`eval_set_error("no method ... on text")` and returned `-1` (`VAL_NONE`), which
reads back as `0` for ints and as the *receiver unchanged* for text. So
`"café,".byte_at(3)` returned **0 for every index**, and `"abcdef".slice(1,3)`
returned `"abcdef"`.

## Root cause

`fn eval_text_method(receiver: i64, method_name: text, arg_eids: [i64]) -> i64`
was defined in **two** files:

| File | Arms | Status |
|---|---|---|
| `src/compiler/10.frontend/core/interpreter/eval_methods.spl:315` | 24 | **DEAD** |
| `src/compiler/10.frontend/core/interpreter/_EvalOps/access_literal_assign_eval.spl:20` | 13 | **LIVE** |

The live copy was a strict subset of the dead one.

Why the `_EvalOps` copy wins: the sole call site is
`_EvalOps/call_method_eval.spl:586`, and `call_method_eval.spl` sits in the same
`_EvalOps` package as `access_literal_assign_eval.spl`. Both are re-exported by
`eval_ops.spl`; `access_literal_assign_eval.spl` opens with
`use compiler.frontend.core.interpreter.eval_ops.*`, so the package-local
definition shadows the `eval_methods.spl` one that `__init__.spl:41` re-exports.
`eval_methods.spl` has **no importer that reaches the dispatch path** — its
`eval_method_call` (line 15) is itself shadowed by the `_EvalOps` copy.

## Evidence (behavioural, not source-reading)

Driven through `core_interpret_expr` with the **Rust seed as host**
(`src/compiler_rust/target/bootstrap/simple`, 154 MB canonical build) compiling
**current working-copy** interpreter source. Driver:
`scratchpad/evalops_probe.spl`. The seed is only the *host*; every number below
is produced by the **pure-Simple interpreter** under test.

Note the driver needs 12 explicit wildcard imports (`lexer*`, `parser*`, `ast*`,
`types`, `monomorphize`) because the `__init__.spl` re-export graph is
incomplete — a plain `use compiler.frontend.core.interpreter.*` does not link.

Before the fix:

```
"café,".len()            => 6      kind=i64   (arm present in live copy)
"café,".char_code_at(3)  => 233    kind=i64   (arm present in live copy)
"abcabc".index_of("b")   => 1      kind=i64   (arm present in live copy)
"café,".byte_at(0)       => 0      kind=nil   <-- dead-copy-only arm
"café,".byte_at(3)       => 0      kind=nil
"café,".byte_at(4)       => 0      kind=nil
"abcdef".slice(1, 3)     => 'abcdef' kind=nil <-- returned the receiver
"abcdef".char_at(2)      => 'abcdef' kind=nil
"1234".parse_int()       => 0      kind=nil
"abc".to_upper()         => 'abc'  kind=nil
"ABC".to_lower()         => 'ABC'  kind=nil
"abc".to_string()        => 'abc'  kind=nil
"abcabc".find("b")       => 0      kind=nil
"abcabc".rfind("b")      => 0      kind=nil
"abcabc".last_index_of("b") => 0   kind=nil
"abcabc".find_str("b")   => 0      kind=nil
```

The `kind=nil` / value-unchanged split is exactly the signature of a missing
dispatch arm: presence in the live copy predicts success with 100% accuracy
across 16 probes.

### Decisive test: sabotage in both directions

Both copies share a `len` arm, so `len` is the control.

| Sabotage | Result | Reading |
|---|---|---|
| `eval_methods.spl` `len` arm → `4242` | `"café,".len()` still **6** | dead |
| `_EvalOps/...` `len` arm → `7373` | `"café,".len()` → **7373** | **live** |

After the fix, the same 16 probes return `99 / 195 / 169 / 44 / 0 / 0` for
`byte_at`, `'bc'` for `slice(1,3)`, `'c'` for `char_at(2)`, an `Option` struct
for `parse_int`, `'ABC'`/`'abc'` for `to_upper`/`to_lower`, and `1 / 4 / 4 / 1`
for `find` / `rfind` / `last_index_of` / `find_str`.

### A second fix was resurrected in passing

The `text-split-limit-ignored` (2026-07-20) splitn fix had been written into
`eval_methods.spl` and therefore never took effect. Ported to the live copy and
verified: `"a:b:c".split(":", 2)[1]` now returns `'b:c'` (was `'b'`).

## Secondary defect: a green spec pinning dead code

`test/01_unit/compiler/interpreter/text_byte_at_dispatch_spec.spl` asserted
structurally against `eval_methods.spl` — the file that does not run. It was
green while the interpreter's `byte_at` returned 0 for every index. This is the
false-green shape this campaign keeps hitting: a structural spec is only as good
as its choice of file, and nothing in the spec framework checks that the file it
reads is on a live path.

## Fix

1. Added the missing arms to the LIVE copy
   (`_EvalOps/access_literal_assign_eval.spl`), semantics matched against the
   seed (`src/compiler_rust/.../interpreter_method/string.rs`) and the C runtime
   (`src/runtime/runtime_native.c`).
2. **Deleted the dead copy** from `eval_methods.spl` rather than keeping the two
   in sync. Justification below.
3. Repointed `text_byte_at_dispatch_spec.spl` at the live file, and added a
   *dispatch-liveness* assertion: the spec now also asserts `eval_methods.spl`
   does **not** define `eval_text_method`, so re-introducing a shadow copy turns
   the spec red instead of silently re-creating the trap.

## `char_at` — deliberate divergence, do NOT "fix" toward the seed

The seed's `char_at` is `chars().nth(idx)` (character-indexed). The C runtime's
`rt_string_char_at` is a raw one-byte slice (byte-indexed). They disagree on
non-ASCII. The interpreter matches the **runtime**, because native/JIT lower to
the runtime and interpreter/native agreement is the property that matters for a
compiler lane. Changing it toward the seed would break that agreement. Recorded
here and in a comment at the arm.

## Is the duplication load-bearing? No.

Checked before deleting:
- The two copies were not specialised — the live one was a *prefix subset*, same
  parameter list, same return convention, same helper calls. No behavioural
  divergence was intended.
- `eval_methods.spl`'s copy had **zero reachable callers**: the only in-repo
  caller of `eval_text_method` is `_EvalOps/call_method_eval.spl:586`, which
  resolves package-locally.
- The duplication was pure split-drift: `eval_ops.spl` was split into `_EvalOps/`
  to stay under the 800-line source limit, and the text-method block was copied
  rather than moved, leaving `eval_methods.spl` as an orphan.

Keeping two copies "in sync" was already tried by `113f0864c7a` (which fixed
`char_code_at` in both) and is exactly what let this drift persist. One
definition is the fix.

The whole file was dead, not just the one function. All four of its functions
were shadowed by strictly-larger `_EvalOps/call_method_eval.spl` versions, and
its 2-arg `eval_method_with_args` overload had callers only inside itself:

| `eval_methods.spl` fn | `_EvalOps/call_method_eval.spl` | Verdict |
|---|---|---|
| `eval_method_call:15` | `:567` | shadowed |
| `eval_method_with_args:197` (2-arg) | `:656` (4-arg) | only self-callers |
| `eval_array_method:250` — 5 arms | `:788` — 12 arms | shadowed subset |
| `eval_text_method:315` — 24 arms | *(this file)* — 13 arms | shadowed **superset** |

Note `eval_array_method` shows the *same* drift with the polarity reversed, so
this was systemic split-drift, not a one-off. After deleting the file, array
methods, split, and text dispatch were all re-probed and are unchanged/correct.

### The strongest argument for deletion: it was actively misleading

At least **five** prior bug docs cite `eval_methods.spl` as *the* self-hosted
interpreter implementation and drew conclusions from reading it —
`run_vs_test_harness_divergence_2026-07-28.md` ("Self-hosted `eval_text_method`
(`eval_methods.spl:298`): 18 arms"), `deep_recheck_2026-07-05.md` (×3),
`jit_string_length_var_control_flow_wrong_value_2026-07-17.md`,
`native_string_methods_unresolved_in_mir_2026-07-17.md`,
`option_pattern_accepted_on_non_option_scrutinee_2026-07-27.md`, and
`bug_db.sdn`'s `text-split-limit-ignored` entry. Every one of those analysed
code that does not execute. A dead file that reads like the canonical one is
worse than no file.

## Verification of the spec itself (it can fail)

Both new guards were sabotaged once each and observed red, then restored.
Engine: **Rust seed child** (`src/compiler_rust/target/bootstrap/simple test`) —
the only engine the suite reaches; `bin/simple` has no `test` subcommand at HEAD.

| Sabotage | Result |
|---|---|
| baseline | `Results: 4 total, 4 passed, 0 failed` |
| `byte_at` arm reverted to slice-then-decode | `4 total, 3 passed, 1 failed` — *"the LIVE interpreter dispatch table has a byte_at arm reading raw bytes"* |
| `eval_methods.spl` restored (shadow re-added) | `4 total, 3 passed, 1 failed` — *"keeps eval_text_method single-definition..."* |
| restored | `4 total, 4 passed, 0 failed` |

`text_char_code_at_codepoint_spec.spl` (3/3) and `nested_string_split_spec.spl`
(1/1) also green.

## Adjacent gap found, NOT fixed here

`eval_int_method` (`call_method_eval.spl:930`) is exported by neither
`__init__.spl` nor `eval_ops.spl`, so an out-of-tree driver that reaches
`core_interpret_expr` fails with `function 'eval_int_method' not found` on any
int method (`(42).to_text()`). Pre-existing — it never lived in the deleted file
— and the same incompleteness that forces a driver to write 12 explicit wildcard
imports. Out of scope for this fix; recorded so it is not rediscovered as a
regression from the deletion.

## Lesson

A structural spec must assert *dispatch liveness*, not just source content.
"Function X in file Y has property P" is worthless if nothing calls file Y's X.
Where a behavioural probe is possible (it was here, via `core_interpret_expr`),
the behavioural probe is the evidence and the structural assertion is only a
regression pin.
