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

## Contamination audit of citing docs (2026-08-01)

Every doc in the tree citing `eval_methods.spl` was re-derived against the live
files. Anchored sweep: `/usr/bin/grep -rn "eval_methods" doc/` — **16 files**,
which is more than the 10 originally suspected. Classification below; each
corrected doc carries an inline note pointing back here.

### NOW-WRONG — a claimed interpreter arm did not exist in the live copy

| Doc | Claim | Live reality |
|---|---|---|
| `deep_recheck_2026-07-05.md` | **P0** `unwrap()` returns `__tag` not `__payload` → `Ok(42).unwrap()` = 5, "silent-wrong-value", at `eval_methods.spl:112` | The live `eval_method_call` (`_EvalOps/call_method_eval.spl:567-654`) has **no Option/Result built-in block at all** — no `unwrap`, `unwrap_or`, `is_some`, `is_none`, `unwrap_err`, `is_ok`, `is_err` anywhere under `interpreter/`. The live path errors loudly (`no method 'unwrap' on struct`); it does not return a wrong value. Same doc's `Array.map`/`reduce` item is half stale: `map`/`filter`/`flat_map`/`any`/`all`/`enumerate` exist live, `reduce` does not. |
| `option_pattern_accepted_on_non_option_scrutinee_2026-07-27.md` | "Option handling is gated on `kind == VAL_STRUCT`, `unwrap_or` falls through returning the receiver" | Same as above — the mechanism described never ran. **The bug's own symptom is unaffected**: it now points squarely at the `rt_unwrap_or_self` MIR lowering, which was measured on live code. Second citation (`last_index_of` "builtin intercepts first") was false during 07-27 → 08-01 (no live arm), true again after `f97dfbbb8ee`. |
| `native_string_methods_unresolved_in_mir_2026-07-17.md` | "`to_upper` **is** handled in the tree-walking interpreter" — the reason the gap was scoped to MIR only | The live text table had **no `to_upper`** until `f97dfbbb8ee`. `to_upper` was missing from MIR *and* the interpreter; only `cg_expr.spl` had it. **Widens the defect**; removes the interpreter as the reference implementation that paragraph leaned on. MIR gap itself unaffected. |
| `char_code_at_quadratic_scan_and_core_string_ascii_probe_2026-07-30.md` (§ mitigations) | "`byte_at` — O(1) direct buffer read on **all four** lanes" | The live text table had **no `byte_at`** on 2026-07-30. `s.byte_at(i)` fell through to `eval_set_error` → `-1`/`VAL_NONE`, silently. The document's own recommendation ("use `byte_at` to escape the quadratic scan") was **not viable on the interpreter lane** when written; viable only from `f97dfbbb8ee`. |
| `run_vs_test_harness_divergence_2026-07-28.md` | "Self-hosted `eval_text_method`: **18 arms**, 18/18 probed" | The live table had **11** arms; 11 were missing and silently error-returning. The "18/18 probed" figure measured the Rust seed, as that section's own preceding paragraph states. That doc's *warning* about duplicate tables was right — it just under-counted the duplication (all four functions, not one). |
| `text_len_bytes_vs_index_codepoints_2026-07-02.md` | self-hosted interpreter `char_at` = **codepoint**-indexed with a byte guard | (1) No live `char_at` existed on 2026-07-02 — the row should have read "absent". (2) The `char_at` added by `f97dfbbb8ee` is deliberately **BYTE**-indexed, agreeing with the C runtime and diverging from the seed — the opposite alignment. The *guard*-unit half of the finding survives and step 2 of its migration plan still applies. |

### CONTAMINATED — evidence came from dead code, conclusion SURVIVES

| Doc | Verdict |
|---|---|
| `array_at_method_missing_dash_path_2026-07-20.md` | **The "seed-only" framing does NOT collapse.** It cited `eval_methods.spl:296` *and* `_EvalOps/call_method_eval.spl:830`; the live `eval_array_method` genuinely carries the `at` arm and is a strict **superset** of the dead copy (adds `map`/`filter`/`flat_map`/`any`/`all`/`enumerate`). "The pure-Simple interpreter already implements `.at()` correctly" **holds**, and the held patch is still the right patch. New caveat recorded there: **text** `.at` is absent from the live table in *both* copies, so on text `.at` the engines diverge the other way. |
| `array_at_returns_nil_for_every_index_2026-08-01.md` | Same — only the "in **both** of its method-eval paths" redundancy claim was false. There was one live path. |
| `char_code_at_quadratic_scan_..._2026-07-30.md` § (f) | The byte-indexed `char_code_at` snippet was quoted from the dead file, but the live copy had the **same defect in a different shape** (`s.substring(idx, idx+1)` vs `s[idx:idx+1]`). Verdict "(f) pure-Simple `char_code_at` is byte-indexed" **survives**. |
| `text_index_of_start_arg_dropped_..._2026-07-28.md` | `eval_methods.spl:466-473` appeared only in an "all other sites are arity-1" inventory. Dropping it changes nothing: the sole live 2-arg-aware dispatcher is still `_EvalOps/access_literal_assign_eval.spl`, still self-delegating. |
| `2026-08-01_interpreter_char_code_at_byte_indexed.md` | Its history was already **accurate** — it is the doc that first measured "fixing `eval_methods.spl` changed nothing observable". Extended with the deletion, and its filed follow-up marked done. |
| `open_bug_doc_staleness_audit_2026-07-27.md` | One row's `eval_methods.spl:107` evidence retracted; the `method_calls_literals.spl` half was live-measured, so the STILL-OPEN verdict stands. |

### HARMLESS — incidental path in a file list or site count

`text_index_alignment_rescope_2026-07-30.md` (lane file list),
`text_index_census_stage1_2026-07-30.md` (lane family list — note added that
the live arm did not honour the 2-arg `start` form at census time),
`if_chain_last_arm_returns_previous_value_2026-07-28.md` (site count 43 → 40),
`jit_string_length_var_control_flow_wrong_value_2026-07-17.md` (×3 sites struck).

### `bug_db.sdn` — do NOT hand-edit

`doc/08_tracking/bug/bug_db.sdn` carries a `#sdn-crc32:` integrity header and
is regenerated by the `bin/simple bug-add` / `bin/simple bug-gen` tooling (see
`.claude/rules/structure.md` § Auto-Generated Docs). Hand-editing invalidates
the CRC. Its single stale citation is in the `text-split-limit-ignored`
description, which says the splitn fix was applied to "the self-hosted .spl
interpreter (`eval_methods.spl`)". **The stale path does NOT self-heal** — the
description is free text captured at `bug-add` time and no regeneration pass
rewrites it. **The conclusion is nevertheless intact**: verified that the
splitn-semantics `limit` handling *is* present in the live
`_EvalOps/access_literal_assign_eval.spl` split arm (`arg_eids.len() > 1`,
keep first `limit-1`, rejoin remainder), so the recorded fix landed on live
code. Correct the path via `bin/simple bug-add --id=text-split-limit-ignored`
(or the equivalent update path), not by editing the `.sdn`.

### One thing this audit did NOT settle (UNKNOWN)

Whether the deleted `eval_method_call` ever executed. The sabotage proof
covered `eval_text_method`, whose sole call site (`call_method_eval.spl:586`)
is inside `_EvalOps` — package-local shadowing there is decisive.
`eval_method_call`'s only external caller is `eval.spl:301`, **outside**
`_EvalOps`, and how that resolved between the re-export and the package-local
copy was never measured. **What would settle it: nothing anymore** — one
definition survives. What matters going forward is the *current* state, which
is measurable and is stated above.

### Actionable gap this audit surfaced

**Option/Result built-in methods are entirely absent from the pure-Simple
interpreter.** `grep '"unwrap"' src/compiler/10.frontend/core/interpreter/`
returns nothing; the only `Option::Some` mentions are in `eval.spl:116`
(pattern matching) and `eval_access.spl:553` (construction). Any Simple source
calling `.unwrap()` / `.unwrap_or()` / `.is_some()` / `.is_none()` /
`.is_ok()` / `.is_err()` on an Option/Result **struct** value errors under the
pure-Simple interpreter today. Whether this is a regression from the deletion
or a long-standing gap is the UNKNOWN above; either way the fix belongs in
`_EvalOps/call_method_eval.spl`, and it must not be rediscovered by reading
the deleted file out of git history. Also still open: `Array.reduce` is
unimplemented in the live `eval_array_method`.

## Lesson

A structural spec must assert *dispatch liveness*, not just source content.
"Function X in file Y has property P" is worthless if nothing calls file Y's X.
Where a behavioural probe is possible (it was here, via `core_interpret_expr`),
the behavioural probe is the evidence and the structural assertion is only a
regression pin.

**Corollary from the audit above:** a dead duplicate does not just waste space,
it *manufactures false negatives across the doc tree*. Six separate
investigations concluded "the interpreter already handles this" from a file
that never ran, and in four of those the live interpreter had **no such arm at
all** — so the true defect was consistently recorded as narrower than it was.
When deleting a shadowed duplicate, sweep every doc that cites it in the same
change.
