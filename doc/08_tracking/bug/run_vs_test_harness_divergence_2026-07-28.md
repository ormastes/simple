# `bin/simple run` vs `bin/simple test` — harness divergence measurement (2026-07-28)

**Status:** MEASURED. No fixes applied (measurement task).
**Binary under test:** `bin/simple` -> `bin/release/x86_64-unknown-linux-gnu/simple`,
built `2026-07-27 22:06`, prints the *"Rust-built Simple binary is a bootstrap
seed only"* banner. Both `run` and `test` are the SAME binary — the divergence
is entirely internal.
**Probe files:** `build/probe_divergence/` (`cases.txt`, `fast_driver.shs`,
`probe_driver.shs`, per-case `f_*.spl` / `p_*.spl` / `s_*.spl` + logs).

---

## 1. The split, named

| | `bin/simple run <file>` | `bin/simple test <spec>` |
|---|---|---|
| Engine | **Cranelift JIT** (default) | **tree-walk interpreter**, always |
| Selected at | `driver/src/exec_core.rs:629-660` (`run_file_with_args`) | `driver/src/cli/test_runner/types.rs:292` — `execution_mode: TestExecutionMode::Interpreter` is the hard default |
| Method dispatch table | `compiler/src/codegen/instr/calls.rs` (method name -> `rt_*` symbol), `codegen/instr/methods.rs`, `codegen/instr/closures_structs.rs`, `codegen/llvm/functions.rs` | `compiler/src/interpreter_method/collections.rs`, `interpreter_method/string.rs`, `interpreter_helpers/method_dispatch.rs` |
| Can the spec suite reach the other engine? | — | **NO.** `TestExecutionMode` has exactly four variants — `Interpreter`, `Smf`, `Native`, `Composite` (`types.rs:57-67`). There is **no JIT test-execution mode**. |

**Headline:** the engine that ordinary programs run on (`run` -> JIT) is
**structurally unreachable from the spec suite**. Every green `N examples, 0
failures` in this repo is evidence about the interpreter only.

### A/B knobs — one works, one is a decoy

| Knob | Effect on this binary | Why |
|---|---|---|
| `SIMPLE_NO_JIT=1` | **NO-OP.** Broken output stays broken. | Read only by the *pure-Simple* interpreter, `src/compiler/10.frontend/core/interpreter/mod.spl:194`. **No reader anywhere in `src/compiler_rust/`.** |
| `SIMPLE_EXECUTION_MODE=interpreter` | **WORKS** — reproduces the spec harness engine exactly. | `exec_core.rs:875` + execution-mode plumbing. |
| `SIMPLE_EXECUTION_MODE=jit` | Forces JIT (also bypasses the `should_prefer_interpreter_for_source` auto-demotions). | `exec_core.rs:871-878` |

Use `SIMPLE_EXECUTION_MODE`, never `SIMPLE_NO_JIT`, when A/B-ing this binary.

### Silent whole-program engine demotion

`run_file_with_args` demotes the **entire program** to the interpreter on any
JIT failure and prints only `[INFO] JIT compilation failed, falling back to
interpreter: ...` on stderr. An unresolved `rt_dict_insert` from a *single*
`d.insert(...)` anywhere in the module makes every other method in that program
silently switch engines and start answering correctly. **This masked the whole
bug class in the first version of this probe** — the initial 44-line combined
probe reported 38/38 AGREE purely because one `dict.insert` had demoted it.
Every probe below is therefore its own single-method program.

Two more auto-demotion triggers, keyed on **source text**, not semantics
(`exec_core.rs:881-901`): a source containing `get_cli_args`, `rt_cli_get_args`
or `std.cli`, and a source containing `window_winit`. Adding an unrelated
`use std.cli` to a file changes which engine evaluates the whole file.

---

## 2. Divergence table

Method-by-method, same binary, byte-identical evaluation body, one program per
row. `run` column = `SIMPLE_EXECUTION_MODE=jit` (the `bin/simple run` default);
`test` column = the spec-harness engine. Literal output is recorded verbatim —
a wrong answer here typically presents as a leaked tag box or a shifted int, not
a clean sentinel.

Correctness note: **the `test`/interpreter column is correct in every DISAGREE
row below**; the JIT column is the wrong one in all of them.

Both drivers ran all 60 cases to completion and agree 60/60 (see §7), so the
table below is the real `bin/simple run` vs real `bin/simple test` result, not
an extrapolation.

| Probe | receiver | `run` (JIT) | `test` (interp) | verdict |
|---|---|---|---|---|
| `arr_len` | array | `3` | `3` | AGREE |
| `arr_index_of_first` | array | `<value:0xffffffffffffffff>` | `0` | **DISAGREE** |
| `arr_index_of_mid` | array | `<value:0xffffffffffffffff>` | `1` | **DISAGREE** |
| `arr_index_of_last` | array | `<value:0xffffffffffffffff>` | `2` | **DISAGREE** |
| `arr_index_of_absent` | array | `<value:0xffffffffffffffff>` | `-1` | **DISAGREE** |
| `arr_index_of_empty` | array | `<value:0xffffffffffffffff>` | `-1` | **DISAGREE** |
| `arr_index_of_text` | array | `<value:0xffffffffffffffff>` | `2` | **DISAGREE** |
| `arr_contains_yes` | array | `true` | `true` | AGREE |
| `arr_contains_no` | array | `false` | `false` | AGREE |
| `arr_contains_text` | array | `true` | `true` | AGREE |
| `arr_push_len` | array | `3` | `3` | AGREE |
| `arr_push_last` | array | `3` | `3` | AGREE |
| `arr_enumerate_len` | array | `-1` (+ stderr `Runtime error: Function 'Array.enumerate' not found`, **exit 0**) | `3` | **DISAGREE** |
| `arr_index0` | array | `10` | `10` | AGREE |
| `arr_index_last` | array | `30` | `30` | AGREE |
| `arr_first` | array | `80` | `10` | **DISAGREE** (`10 << 3` — tag-boxed int returned raw) |
| `arr_last` | array | `240` | `30` | **DISAGREE** (`30 << 3`) |
| `arr_pop` | array | `24` | `3` | **DISAGREE** (`3 << 3`) |
| `arr_reverse` | array | `30` | `30` | AGREE |
| `arr_sort` | array | `10` | `10` | AGREE |
| `arr_join` | array | `a-b` | `a-b` | AGREE |
| `arr_slice` | array | `2` | `2` | AGREE |
| `arr_is_empty` | array | `true` | `true` | AGREE |
| `arr_map` | array | `3` (+ stderr `Runtime error: Function 'Array.map' not found`, **exit 0**) | `2` | **DISAGREE** |
| `arr_filter` | array | **SIGSEGV (exit 139)** | `2` | **DISAGREE** |
| `arr_any` | array | **SIGSEGV (exit 139)** | `true` | **DISAGREE** |
| `arr_all` | array | **SIGSEGV (exit 139)** | `true` | **DISAGREE** |
| `dict_keys_len` | dict | *JIT bailout* -> `2` | `2` | **UNMEASURED** on JIT |
| `dict_values_len` | dict | *JIT bailout* -> `2` | `2` | **UNMEASURED** on JIT |
| `dict_contains_key_yes` | dict | *JIT bailout* -> `true` | `true` | **UNMEASURED** on JIT |
| `dict_contains_key_no` | dict | *JIT bailout* -> `false` | `false` | **UNMEASURED** on JIT |
| `dict_get_or_present` | dict | *JIT bailout* -> `1` | `1` | **UNMEASURED** on JIT |
| `dict_get_or_absent` | dict | *JIT bailout* -> `-7` | `-7` | **UNMEASURED** on JIT |
| `dict_index_read` | dict | *JIT bailout* -> `2` | `2` | **UNMEASURED** on JIT |
| `dict_len` | dict | *JIT bailout* -> `2` | `2` | **UNMEASURED** on JIT |
| `dict_insert_then_keys` | dict | *JIT bailout* -> `2` | `2` | **UNMEASURED** on JIT |
| `dict_index_write` | dict | *JIT bailout* -> `2` | `2` | **UNMEASURED** on JIT |
| `dict_get` | dict | *JIT bailout* -> `1` | `1` | **UNMEASURED** on JIT |
| `text_len` | text | `11` | `11` | AGREE |
| `text_contains_yes` | text | `true` | `true` | AGREE |
| `text_contains_no` | text | `false` | `false` | AGREE |
| `text_index_of_present` | text | `2` | `2` | AGREE |
| `text_index_of_first` | text | `0` | `0` | AGREE |
| `text_index_of_absent` | text | `-1` | `-1` | AGREE |
| `text_substring` | text | `hello` | `hello` | AGREE |
| `text_slice` | text | `hello` | `hello` | AGREE |
| `text_starts_with` | text | `true` | `true` | AGREE |
| `text_ends_with` | text | `true` | `true` | AGREE |
| `text_replace` | text | `hello there` | `hello there` | AGREE |
| `text_split_len` | text | `2` | `2` | AGREE |
| `text_strip` | text | *no output* — stderr `Runtime error: Function 'str.strip' not found` | `pad` | **DISAGREE** |
| `text_to_upper` | text | `hello` (silent no-op, **no error, exit 0**) | `HELLO` | **DISAGREE** |
| `text_to_lower` | text | `abc` | `abc` | AGREE |
| `text_char_code_at` | text | `104` | `104` | AGREE |
| `text_lines_len` | text | `-1` | `3` | **DISAGREE** |
| `text_char_at` | text | `e` | `e` | AGREE |
| `text_find_str` | text | `2` | `2` | AGREE |
| `text_rfind` | text | `3` | `3` | AGREE |
| `text_parse_int` | text | `0.00000000000000000` | `42` | **DISAGREE** (returns a *float-formatted* zero) |
| `text_to_string` | text | `hi` | `hi` | AGREE |

### Totals

| | count |
|---|---|
| Probes run | **60** |
| AGREE | **31** |
| DISAGREE | **18** |
| UNMEASURED on JIT (whole-program bailout) | **11** (every dict probe) |

By receiver: array **14 DISAGREE / 27** (13 AGREE), text **4 DISAGREE / 22**
(18 AGREE), dict **0 measurable / 11** (the JIT cannot compile *any* dict operation on this
binary — every dict probe bailed out on an unresolved `rt_dict_*` symbol).

Set receivers: **no `eval_set_method` / set dispatch table exists** in either
engine. Sets are not a distinct receiver kind here; nothing to measure.

---

## 3. Failure modes observed (all four are silent-by-default)

1. **Leaked tag box** — `<value:0xffffffffffffffff>`. All six `index_of`
   rows. `0xffffffffffffffff` is `-1`, returned as an `i64` but consumed as a
   boxed `RuntimeValue`.
2. **Shifted int** — `arr_first`/`arr_last`/`arr_pop` return `v << 3`
   (`10 -> 80`, `30 -> 240`, `3 -> 24`): a tag-boxed int handed back without
   decoding. Prints as a plausible number; nothing flags it.
3. **`Function 'X' not found` on stderr with exit code 0** — `Array.map`,
   `Array.enumerate`, `str.strip`. The program keeps running and prints a
   garbage value. Verified: `arr_map`, `arr_enumerate_len` both exit 0.
4. **Silent no-op** — `text_to_upper` returns the receiver unchanged with **no
   diagnostic at all**. The worst of the four; indistinguishable from success.
5. **SIGSEGV** — `filter`/`any`/`all` with a lambda (exit 139).

---

## 4. Missing / mis-wired arm locations

| Symptom | Location |
|---|---|
| `[T].index_of` -> tag box | `src/compiler_rust/compiler/src/codegen/instr/calls.rs:3230` maps `"index_of" => "rt_index_of"`, and `rt_index_of` (`src/compiler_rust/runtime/src/value/collections.rs:3051`) is correct and returns `I64` per `codegen/runtime_sffi.rs:416`. **The source is already fixed; the deployed binary is stale.** `calls.rs` mtime `07-28 00:38` and `collections.rs` `07-28 00:37` are both NEWER than the binary (`07-27 22:06`), and both files are `M` in git. A rebuild should close all six `index_of` rows. |
| `Array.map` / `Array.enumerate` / `str.strip` "not found" | No arm in the JIT method->`rt_*` table: `src/compiler_rust/compiler/src/codegen/instr/calls.rs` (~L3200-3260) and the parallel tables `codegen/instr/methods.rs`, `codegen/instr/closures_structs.rs:1226`, `codegen/llvm/functions.rs:2275`. The interpreter equivalents exist at `compiler/src/interpreter_method/collections.rs` and `interpreter_method/string.rs`. **Four parallel dispatch tables must be kept in sync by hand — that is the structural cause of this whole bug family.** |
| `first`/`last`/`pop` shifted `<< 3` | `calls.rs` maps `"first" => rt_array_first`, `"last" => rt_array_last`; the arms exist, so this is a **return-type tag** bug (declared as `I64` in `codegen/runtime_sffi.rs` while the runtime returns a boxed `RuntimeValue`, or vice versa), not a missing arm. |
| `text.to_upper` no-op / `parse_int` float-zero | `calls.rs:3224-3226` maps `"to_upper"|"upper" => rt_string_to_upper` and `"to_int"|"to_i64"|"parse_int" => rt_string_to_int`. Arms present, results wrong -> same return-type/ABI class as above. |
| every dict op unresolvable under JIT | `rt_dict_insert` (and siblings) not registered in `src/compiler_rust/compiler/src/codegen/runtime_sffi.rs` for the Cranelift module. |

Note the two *duplicate* self-hosted interpreter tables in the pure-Simple tree
as well — `src/compiler/10.frontend/core/interpreter/eval_methods.spl:248` and
`src/compiler/10.frontend/core/interpreter/_EvalOps/call_method_eval.spl:788`
both define `eval_array_method`, with **different** arm sets (the former has 4
arms, the latter 11). Neither is exercised by `bin/simple` today because
`bin/simple` is the Rust seed, but the same sync-by-hand hazard applies once the
pure-Simple binary is deployed.

---

## 5. Method coverage vs. what exists

Dispatch-table arm counts, from reading the tables rather than guessing:

- Self-hosted `eval_array_method` (`_EvalOps/call_method_eval.spl:788`): 11 arms
  — `len`, `push`, `contains`, `index_of`, `map`, `filter`, `flat_map`/`flatmap`,
  `any`, `all`, `enumerate`. **10/11 probed** (`flat_map` not probed).
- Self-hosted `eval_dict_method` (`call_method_eval.spl:594`): 7 arms — `len`,
  `keys`, `values`, `contains_key`, `get`, `get_or`, `insert`. **7/7 probed.**
- Self-hosted `eval_text_method` (`eval_methods.spl:298`): 18 arms — `len`,
  `contains`, `char_code_at`, `substring`, `slice`, `starts_with`, `ends_with`,
  `replace`, `split`, `lines`, `strip`, `find_str`, `rfind`, `char_at`,
  `parse_int`, `to_upper`, `to_lower`, `to_string`, `index_of`.
  **18/18 probed.**
- Plus array methods that exist only in the Rust tables (`first`, `last`, `pop`,
  `sort`, `reverse`, `join`, `slice`, `is_empty`) — all probed.

**Coverage: 60 probes over 36 distinct dispatch-table arms + 8 Rust-only array
methods. The only listed arm not probed is `flat_map`.**

---

## 6. Verdict on spec-based evidence

**Spec evidence in this repo is trustworthy ONLY as evidence about the
interpreter.** It says nothing about the engine `bin/simple run` uses, and it
cannot be made to, because `TestExecutionMode` has no JIT variant.

For **array receivers** the gap is severe: 14 of 27 array probes disagree, and
the disagreements include silent wrong answers (`first`, `last`, `pop`,
`to_upper`) that no assertion, exit code, or stderr line would catch. A green
array spec is close to zero evidence about `run` behaviour.

For **dict receivers** the JIT path is not merely untested, it is
**non-functional** — every dict operation forces a whole-program engine
demotion. Any `run`-side program that touches a dict silently executes under a
different engine than the one it was compiled for.

For **text receivers** the interpreter/JIT agreement is much better (18/22),
but the four failures include the completely silent `to_upper` no-op.

### Real-world exposure in the existing suite

Spec files under `test/` that call at least one method measured as divergent
(`index_of`, `enumerate`, `first`, `last`, `pop`, `map`, `filter`, `any`, `all`,
`strip`, `to_upper`, `lines`, `parse_int`):

**711 of 23,958 spec files (≈3.0%).** Breakdown (files containing the token):
`index_of` 359, `map(` 205, `filter(` 183, `parse_int` 69, `pop()` 66,
`enumerate` 58, `any(` 44, `first()` 42, `last()` 39, `all(` 29, `strip()` 6,
`lines()` 3, `to_upper()` 0.

These 711 files are green today and would remain green after any JIT-side
regression in those methods, because the suite never runs the JIT engine. This
is the practical size of the blind spot, not a count of currently-broken specs.

### Recommended follow-ups (not done here — measurement task)

1. Rebuild `bin/simple` from current `src/compiler_rust/`. This alone should
   close the six `index_of` rows; re-run `build/probe_divergence/fast_driver.shs`
   to confirm and to see what else moves.
2. Add a `TestExecutionMode::Jit` variant so specs can run on both engines, and
   run at least the language/stdlib tier under both.
3. Make the JIT dispatch table fail **closed**: `Function 'X' not found` must be
   a hard error, not a stderr line followed by exit 0 and a garbage value.
4. Collapse the four parallel Rust dispatch tables (`calls.rs`, `methods.rs`,
   `closures_structs.rs`, `llvm/functions.rs`) behind one table; the sync-by-hand
   duplication is the root cause of this whole family.
5. Retire or wire up `SIMPLE_NO_JIT` — a documented knob that silently does
   nothing actively produced a wrong root-cause conclusion during this
   investigation.

---

## 7. Reproduction

```sh
sh build/probe_divergence/fast_driver.shs   # ~3 min, JIT vs interpreter, 60 cases
sh build/probe_divergence/probe_driver.shs  # ~90 min, real `run` vs real `test`
```

`fast_driver` substitutes `SIMPLE_EXECUTION_MODE=interpreter` for the spec
harness; `probe_driver` uses the real `bin/simple run` and `bin/simple test`.

**Both drivers completed all 60 cases and agree on every value, 60/60.** The
real-harness tallies are identical to the table above: **31 AGREE, 18 DISAGREE,
11 UNMEASURED-on-JIT**. (A naive string diff of the two TSVs reports 15
differences; all 15 are annotation-only — `fast_driver` appends `exit=139` and
`<via-jit-bailout>` markers that `probe_driver` records in its separate engine
column instead. No semantic value differs.) `probe_driver` independently tagged
all 11 dict rows `interp-fallback`, confirming from the real `run` path that the
JIT cannot compile any dict operation.

### Measurement integrity checks

- **Zero-example false green:** `probe_driver` treats a spec with no
  `N examples` line, or with `0 examples`, as `<UNMEASURED>` — never as
  agreement. **0 of 60 specs hit either condition**; every one reported
  `1 example, 0 failures` and emitted its `VALUE=` line.
- **Assertion calibration:** a deliberately-wrong spec
  (`expect(a.index_of(10)).to_equal(999)`) was run through `bin/simple test` and
  **did fail** — `expected 0 to equal 999`, `1 example, 1 failure`, exit 1. The
  spec harness genuinely evaluates `it` bodies and assertions; it is not
  file-load-only. (`.claude/rules/testing.md` still carries an "interpreter mode
  only verifies file loading, NOT `it` block execution" caveat — that caveat did
  not hold for this binary and should be re-checked.) The calibration spec is
  not committed; a permanently-red example trains people to ignore the suite.
- All `run`-side output was captured to files and read from the tail — the lint
  and seed-banner preamble is thousands of lines and `| head` would show none of
  the results.

---

## Post-rebuild verification (2026-07-28 10:35)

The dispatch fixes in `173ad044494` landed **unverified** — they are seed
codegen changes and the deployed `bin/simple` predated them. Rebuilt
`src/compiler_rust/target/debug/simple` (mtime 10:35, `cargo build -p
simple-driver`, exit 0) and re-ran the probes against that binary. One probe
per file, to avoid the whole-program interpreter demotion.

| probe | JIT (before) | JIT (after rebuild) | interpreter | verdict |
|---|---|---|---|---|
| `"hello".to_upper()` | `hello` — silent no-op | **`HELLO`** | `HELLO` | **FIXED** |
| `"  pad  ".strip()` | `Function 'str.strip' not found`, exit 0 | **`[pad]`** | `[pad]` | **FIXED** |
| `[10,20,30].enumerate().len()` | `-1` + not-found, exit 0 | **`3`** | `3` | **FIXED** |
| `[10,20,30].first()` | `80` (`10 << 3`) | **`10`** | `10` | **FIXED** |
| `"hello".index_of("l")` | `2` | `2` | `2` | agrees |
| `[10,20,30].index_of(20)` | `<value:0xff..ff>` | `<value:0xff..ff>` | `1` | **STILL BROKEN** |
| `[text].index_of("y")` | — | **`nil`** | `1` | **STILL BROKEN** |

Positive controls unchanged and correct on both engines after the rebuild:
`.len()` → 3, `.join("-")` → `b-a`, `text.replace` → `yo there`,
`text.to_lower` → `hello`, `[i64].contains(20)` → `true`.

### `index_of` on arrays is NOT fixed, and the dispatch arm was not the cause

All four dispatch tables now map bare `index_of` to `rt_index_of`
(`instr/calls.rs:3234`, `instr/closures_structs.rs:1284`,
`llvm/emitter.rs:192`, `llvm/functions.rs:2275`); `rt_index_of` exists
(`runtime/src/value/collections.rs:3051`) and is declared to codegen
(`runtime_sffi.rs:416`). The only type-qualified `rt_string_find` mapping left
(`llvm/functions.rs:2613`) is correctly gated on a text receiver.

Evidence that the symbol is reached: `text.index_of` returns `2`, and text now
routes through `rt_index_of`.

Evidence that the array path inside it fails: `[i64]` yields a raw `-1`
(`<value:0xffffffffffffffff>`) while `[text]` yields `nil` — two different
wrong answers from one call site, which a simple "not found" cannot explain.

Note for whoever picks this up: **`contains` works on the same array and value**
(`true`), so the array receiver does reach the runtime intact. That is not the
counter-example it first appears to be — there is no `rt_array_contains` at all,
so `contains` takes an entirely different path and proves nothing about
`rt_array_index_of`'s calling convention. The open question is whether
`rt_array_index_of` is entered at all for a typed array receiver, and if so why
`rt_value_eq` fails on JIT-boxed elements.
