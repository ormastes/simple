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

> **This warning was RIGHT, and the hazard fired (audited 2026-08-01).** The
> duplication observed here was not limited to `eval_array_method`: **all four**
> functions in `eval_methods.spl` were duplicated, and in every case the
> `_EvalOps` copy is the one that runs (package-local definitions shadow the
> `__init__.spl` re-export; proven by sabotage in both directions). The
> `eval_methods.spl` copies never executed. It was deleted in `f97dfbbb8ee`.
> The one arm-count in this document that was read off the **dead** file is
> corrected below.

---

## 5. Method coverage vs. what exists

Dispatch-table arm counts, from reading the tables rather than guessing:

- Self-hosted `eval_array_method` (`_EvalOps/call_method_eval.spl:788`): 11 arms
  — `len`, `push`, `contains`, `index_of`, `map`, `filter`, `flat_map`/`flatmap`,
  `any`, `all`, `enumerate`. **10/11 probed** (`flat_map` not probed).
- Self-hosted `eval_dict_method` (`call_method_eval.spl:594`): 7 arms — `len`,
  `keys`, `values`, `contains_key`, `get`, `get_or`, `insert`. **7/7 probed.**
- ~~Self-hosted `eval_text_method` (`eval_methods.spl:298`): 18 arms — `len`,
  `contains`, `char_code_at`, `substring`, `slice`, `starts_with`, `ends_with`,
  `replace`, `split`, `lines`, `strip`, `find_str`, `rfind`, `char_at`,
  `parse_int`, `to_upper`, `to_lower`, `to_string`, `index_of`.
  **18/18 probed.**~~
  **NOW-WRONG — counted from the dead file.** Corrected 2026-08-01. The live
  `eval_text_method` is `_EvalOps/access_literal_assign_eval.spl:44`, and on
  2026-07-28 it had **11** arms, not 18: `len`, `contains`, `char_code_at`,
  `substring`, `starts_with`, `ends_with`, `replace`, `split`,
  `split_lines`/`lines`, `trim`/`strip`, `index_of`. **Missing** were `slice`,
  `find_str`, `rfind`, `char_at`, `parse_int`, `to_upper`, `to_lower`,
  `to_string`, `byte_at`, `last_index_of` and `find` — each falling through to
  `eval_set_error` and returning `-1`/`VAL_NONE` **silently**. The "18/18
  probed" line is therefore not evidence about the pure-Simple lane; the probes
  ran against `bin/simple`, i.e. the Rust seed, exactly as this section's own
  preceding paragraph states. `f97dfbbb8ee` ported the 11 missing arms into the
  live file and deleted the duplicate, so the live count is now ~20. See
  `doc/08_tracking/bug/2026-08-01_interpreter_eval_text_method_duplicate_live_subset.md`.
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

---

# Re-measurement — 2026-07-28 (later same day, post-fix)

The original table above is **kept intact as history**. This section is a fresh
run of the same 60-probe corpus, same probe names, after the `to_upper` /
`strip` / `enumerate` / `first` / `index_of` fixes landed.

## Binary under test

| | |
|---|---|
| Command | `cd src/compiler_rust && cargo build -p simple-driver` |
| Binary | `/home/ormastes/dev/pub/simple/src/compiler_rust/target/debug/simple` |
| mtime | **2026-07-28 11:06:17.100 +0000** |
| Size | 479,899,928 bytes |

**Driver fix (important).** `build/probe_divergence/fast_driver.shs` hardcoded
`$ROOT/bin/simple` — the *deployed* release copy, mtime `2026-07-28 05:45:35`,
which predates this build and does **not** contain the fixes. Measuring through
it would have reproduced the old table and reported the fixes as not landed. The
driver now takes the binary from `PROBE_BIN` (default unchanged), and echoes the
binary path + `ls -l` to stderr at start so every future run self-documents which
artifact produced it. Invocation used:

```sh
PROBE_BIN=$ROOT/src/compiler_rust/target/debug/simple \
PROBE_OUTDIR=$ROOT/build/probe_divergence/fast_0728b \
PROBE_RESULTS=$ROOT/build/probe_divergence/fast_results_0728b.tsv \
  timeout 1800 sh build/probe_divergence/fast_driver.shs
```

Method is otherwise unchanged: one method per probe file, `SIMPLE_EXECUTION_MODE=jit`
vs `SIMPLE_EXECUTION_MODE=interpreter` on the same source, output captured to
files, `$?` taken from the command under test, `timeout 120` per run.

## Silent-fallback audit

Every one of the 60 JIT logs was re-grepped independently of the driver for
`JIT compilation failed` and `JIT panicked`:

**0 probes fell back to the interpreter.** No probe in this run is a false AGREE
caused by a demoted program, and nothing is reported as UNMEASURED.

This is also confirmed at the source level: `should_prefer_interpreter_for_source`
(`driver/src/exec_core.rs`) returns `false` as soon as `SIMPLE_EXECUTION_MODE` is
set, so the heuristic interpreter-preemption path cannot silently engage here, and
both remaining bailout paths print to stderr.

## Totals

| Verdict | 2026-07-28 (original) | 2026-07-28 (re-measured) | Δ |
|---|---|---|---|
| AGREE | 31 | **51** | +20 |
| DISAGREE | 18 | **9** | −9 |
| UNMEASURED on JIT | 11 | **0** | −11 |

Transition census (all 60 accounted for): 12 `DISAGREE→AGREE`, 8
`UNMEASURED→AGREE`, 3 `UNMEASURED→DISAGREE`, 37 unchanged (31 AGREE + 6 DISAGREE).
**Zero `AGREE→DISAGREE`.**

By receiver: array **4 DISAGREE / 27**, dict **3 DISAGREE / 11**, text
**2 DISAGREE / 22**.

## Full table

| Probe | Recv | JIT (`run`) | Interp (`test`) | Verdict |
|---|---|---|---|---|
| `arr_len` | array | `3` | `3` | AGREE |
| `arr_index_of_first` | array | `0` | `0` | AGREE |
| `arr_index_of_mid` | array | `1` | `1` | AGREE |
| `arr_index_of_last` | array | `2` | `2` | AGREE |
| `arr_index_of_absent` | array | `-1` | `-1` | AGREE |
| `arr_index_of_empty` | array | `-1` | `-1` | AGREE |
| `arr_index_of_text` | array | `2` | `2` | AGREE |
| `arr_contains_yes` | array | `true` | `true` | AGREE |
| `arr_contains_no` | array | `false` | `false` | AGREE |
| `arr_contains_text` | array | `true` | `true` | AGREE |
| `arr_push_len` | array | `3` | `3` | AGREE |
| `arr_push_last` | array | `3` | `3` | AGREE |
| `arr_enumerate_len` | array | `3` | `3` | AGREE |
| `arr_index0` | array | `10` | `10` | AGREE |
| `arr_index_last` | array | `30` | `30` | AGREE |
| `arr_first` | array | `10` | `10` | AGREE |
| `arr_last` | array | `30` | `30` | AGREE |
| `arr_pop` | array | `3` | `3` | AGREE |
| `arr_reverse` | array | `30` | `30` | AGREE |
| `arr_sort` | array | `10` | `10` | AGREE |
| `arr_join` | array | `a-b` | `a-b` | AGREE |
| `arr_slice` | array | `2` | `2` | AGREE |
| `arr_is_empty` | array | `true` | `true` | AGREE |
| `arr_map` | array | `3` (+ stderr `Runtime error: Function 'Array.map' not found`, **exit 0**) | `2` | **DISAGREE** |
| `arr_filter` | array | `0` (**exit 0** — was SIGSEGV 139) | `2` | **DISAGREE** |
| `arr_any` | array | `nil` (**exit 0** — was SIGSEGV 139) | `true` | **DISAGREE** |
| `arr_all` | array | `nil` (**exit 0** — was SIGSEGV 139) | `true` | **DISAGREE** |
| `dict_keys_len` | dict | `2` | `2` | AGREE |
| `dict_values_len` | dict | `2` | `2` | AGREE |
| `dict_contains_key_yes` | dict | `true` | `true` | AGREE |
| `dict_contains_key_no` | dict | `false` | `false` | AGREE |
| `dict_get_or_present` | dict | `error` (+ stderr `Runtime error: Function 'Dict.get_or' not found`, **exit 0**) | `1` | **DISAGREE** |
| `dict_get_or_absent` | dict | `error` (+ stderr `Runtime error: Function 'Dict.get_or' not found`, **exit 0**) | `-7` | **DISAGREE** |
| `dict_index_read` | dict | `2` | `2` | AGREE |
| `dict_len` | dict | `2` | `2` | AGREE |
| `dict_insert_then_keys` | dict | `1` (+ stderr `Runtime error: Function 'Dict.insert' not found`, **exit 0**) | `2` | **DISAGREE** |
| `dict_index_write` | dict | `2` | `2` | AGREE |
| `dict_get` | dict | `1` | `1` | AGREE |
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
| `text_strip` | text | `pad` | `pad` | AGREE |
| `text_to_upper` | text | `HELLO` | `HELLO` | AGREE |
| `text_to_lower` | text | `abc` | `abc` | AGREE |
| `text_char_code_at` | text | `104` | `104` | AGREE |
| `text_lines_len` | text | `-1` (+ stderr `Runtime error: Function 'str.lines' not found`, **exit 0**) | `3` | **DISAGREE** |
| `text_char_at` | text | `e` | `e` | AGREE |
| `text_find_str` | text | `2` | `2` | AGREE |
| `text_rfind` | text | `3` | `3` | AGREE |
| `text_parse_int` | text | `0.000…0002` (float-formatted) | `42` | **DISAGREE** |
| `text_to_string` | text | `hi` | `hi` | AGREE |

## (a) Newly fixed since the last run — 12 probes

All confirmed on the binary above; each was **DISAGREE** and is now **AGREE**.

| Probe | Was | Now |
|---|---|---|
| `arr_index_of_first` | `<value:0xffffffffffffffff>` | `0` |
| `arr_index_of_mid` | `<value:0xffffffffffffffff>` | `1` |
| `arr_index_of_last` | `<value:0xffffffffffffffff>` | `2` |
| `arr_index_of_absent` | `<value:0xffffffffffffffff>` | `-1` |
| `arr_index_of_empty` | `<value:0xffffffffffffffff>` | `-1` |
| `arr_index_of_text` | `<value:0xffffffffffffffff>` | `2` |
| `arr_enumerate_len` | `-1` + "not found", exit 0 | `3` |
| `arr_first` | `80` (`10 << 3`) | `10` |
| `arr_last` | `240` (`30 << 3`) | `30` |
| `arr_pop` | `24` (`3 << 3`) | `3` |
| `text_strip` | no output, `str.strip` not found | `pad` |
| `text_to_upper` | `hello` (silent no-op) | `HELLO` |

Note `arr_last` and `arr_pop` were **not** on the hand-verified list but were
carried along by the same tag-box fix — the `<< 3` family is fixed as a class,
not case by case.

### (a′) Newly measurable and agreeing — 8 dict probes

Formerly UNMEASURED (whole-program JIT bailout), now genuinely compiled by the
JIT and matching the interpreter: `dict_keys_len`, `dict_values_len`,
`dict_contains_key_yes`, `dict_contains_key_no`, `dict_index_read`, `dict_len`,
`dict_index_write`, `dict_get`.

## (b) Still divergent — 6 probes

Unchanged verdicts, carried over from the original table.

| Probe | JIT | Interp | Note |
|---|---|---|---|
| `arr_map` | `3` | `2` | `Array.map` not found; exit 0 |
| `arr_filter` | `0` | `2` | **character changed**: SIGSEGV → silent `0` |
| `arr_any` | `nil` | `true` | **character changed**: SIGSEGV → silent `nil` |
| `arr_all` | `nil` | `true` | **character changed**: SIGSEGV → silent `nil` |
| `text_lines_len` | `-1` | `3` | `str.lines` not found; exit 0 |
| `text_parse_int` | float-formatted `0` | `42` | unchanged |

**The three closure-taking array probes got worse in kind, not in count.**
`arr_filter` / `arr_any` / `arr_all` previously **crashed loudly (exit 139)**.
They now **exit 0 and return a wrong value**. The verdict column is identical, so
a count-only comparison of the two tables shows no change here — but a loud crash
became silent data corruption, which is strictly harder to catch downstream. Do
not read "still DISAGREE" as "unchanged".

## (c) Newly divergent — 3 probes (REGRESSION)

These are the ones that matter, and they are real.

| Probe | Before (via JIT bailout) | Now (JIT compiles it) | Interp |
|---|---|---|---|
| `dict_get_or_present` | `1` ✅ | `error` ❌ | `1` |
| `dict_get_or_absent` | `-7` ✅ | `error` ❌ | `-7` |
| `dict_insert_then_keys` | `2` ✅ | `1` ❌ | `2` |

The verdict transition is `UNMEASURED → DISAGREE`, which is easy to wave away as
"it was never measured, so nothing regressed". **That reading is wrong.** Before,
the JIT could not compile dict at all, bailed out, and the interpreter answered —
so `bin/simple run` printed the *correct* value. Now the JIT compiles the dict
program, does **not** bail out, and `bin/simple run` prints a *wrong* value with
**exit 0**. User-visible `run` behaviour went from correct to silently wrong on
these three. That is a genuine regression introduced alongside the fixes.

Mechanism is the same fail-open pattern in all three: dict *lowering* now
succeeds, but the method bodies are missing (`Function 'Dict.get_or' not found`,
`Function 'Dict.insert' not found`). The runtime prints `Runtime error:` to
stderr and then **continues with exit 0**, so the missing method degrades into a
bad value instead of a failure. `Dict.get_or` and `Dict.insert` are the two
missing symbols.

Zero probes went `AGREE → DISAGREE` — no previously-correct operation broke.

## Is dict still uncompilable on the JIT?

**No — that has changed.** The original run recorded "the JIT cannot compile
*any* dict operation" with all 11 dict probes bailing out. In this run **0 of 11
dict probes bail out**; all 11 compile and execute under Cranelift. 8 agree with
the interpreter, and 3 fail on missing method bodies rather than on compilation.
The blanket dict-bailout finding in the original section is superseded.

## Artifacts

| | |
|---|---|
| Results TSV | `build/probe_divergence/fast_results_0728b.tsv` (name, JIT, interp, jit-exit, interp-exit) |
| Per-probe logs | `build/probe_divergence/fast_0728b/{j,i}_<name>.log` |
| Driver log | `build/probe_divergence/rerun_0728b.log` |
| Corpus | `build/probe_divergence/cases.txt` (unchanged, 60 cases) |

The original `fast_results.tsv` and `fast/` from the first run are left in place.

### Root cause of the three dict "regressions" — unmasked, not newly broken

A follow-up lane isolated the mechanism. The three dict rows above are
**pre-existing JIT bugs that were previously hidden**, not breakage introduced
today. The distinction matters for how they are triaged.

The bail-out message, identical in all 11 dict probes:

```
JIT compilation failed, falling back to interpreter: Cranelift JIT compile:
Module error: unresolved external symbol 'rt_dict_insert' would NULL-jump in JIT;
deferring to interpreter
```

`rt_dict_insert` was declared to codegen (`codegen/runtime_sffi.rs:279`) but
**never existed** in the runtime and was absent from
`common/src/runtime_symbols.rs` — a phantom spec entry, not a feature gap.
Dicts were fully implemented all along.

The demotion is total because the guard at `codegen/jit.rs:101-105`
(`first_unresolved_import`) scans **every declared `Linkage::Import`**, not just
the call sites actually reached. One phantom import therefore demotes the whole
module.

A parallel session fixed it in `0d864c55fe7` by mapping
`"rt_dict_insert" => Some("rt_dict_set")` at `codegen/instr/calls.rs:2787`
(confirmed absent at `0d864c55fe7^`, present at `0d864c55fe7`). Dict code now
genuinely reaches the JIT — 0 of 11 probes bail out, and
`SIMPLE_JIT_TRACE_ADDR=1` shows native compilation.

**That fix is correct, and it unmasks five real JIT correctness bugs:**

| probe | JIT | interpreter |
|---|---|---|
| `{i64:i64}` `contains_key(1)` | `false` | `true` |
| `{i64:i64}` `d[2]` | `3` | `20` |
| `{i64:text}` `d[2]` | *no output* | `y` |
| `{text:i64}` `get_or` hit / miss | `Function 'Dict.get_or' not found` | `1` / `-7` |

All **text**-keyed operations and all i64-key **writes** are correct; only
i64-key **reads** are broken. Cause: the inline-shift list at
`codegen/instr/closures_structs.rs:1361` is
`matches!(runtime_func, "rt_index_get" | "rt_dict_remove" | "rt_contains")`,
omitting `rt_dict_contains` and `rt_dict_get` — so integer keys are hashed
**unboxed on read but boxed on write**.

`get_or` is a different category and must not be fixed the same way: it is
missing from the dict method table at `hir/lower/expr/mod.rs:1085`, but unlike
the `index_of` sibling there is **no `rt_dict_get_or` runtime function**. Adding
the result type alone would emit a call to a nonexistent symbol and re-trigger
the exact demotion just fixed. It needs either a runtime implementation or a
lowering that expands to `contains_key` + `get` + select.

### Correction: the dict key asymmetry is in the WRITE, not the read

The section above says the inline-shift list at
`codegen/instr/closures_structs.rs:1361` omits `rt_dict_contains` and
`rt_dict_get`, and that this is why integer-keyed reads fail. **That is
inverted, and the proposed fix would have been a no-op.**

Verified against the runtime contract and the MIR:

- `rt_dict_get` / `rt_dict_contains` / `rt_dict_set`
  (`runtime/src/value/dict.rs:177,214,240`) all take **tagged** keys, hashed via
  `value_hash` and compared with `rt_value_eq`. Tagged is the contract, so
  boxing is the correct side to change.
- `rt_dict_get` and `rt_dict_contains` **are never emitted by any Cranelift
  lowering.** The only emission sites are `rt_index_get`, `rt_contains` and
  `rt_dict_remove` — all three already in the `box_dict_key` list. Adding the
  two names would have changed nothing.
- `SIMPLE_DUMP_MIR` on `{1: 10, 2: 20}` shows the read already boxed
  (`BoxInt` → `rt_index_get`) and the **write raw**:
  `Call Pure("rt_dict_set") args [dict, ConstInt 1, ConstInt 10]`.
- Decisive probes: `d[0]` on `{0: 99}` works, because `0 << 3 == 0` is the one
  key that survives being stored unboxed; and an index-*write* `d[1] = 10`
  (which does emit `BoxInt`) followed by `d[1]` reads back correctly. Only the
  **literal** write path is raw.

Real cause: `lower_dict_expr` in
`mir/lower/lowering_expr_collection.rs` emits `rt_dict_set` with an unboxed
integer key, unlike every sibling literal lowering (tuple, array) and unlike
every dict read.

### Scope limit of the fix — inferred dicts are still wrong

The fix boxes the key in the dict-literal lowering. It resolves the annotated
case only:

| declaration | expression | JIT | interpreter |
|---|---|---|---|
| `val d: {i64: i64} = {1: 10, 2: 20}` | `d[2].to_string()` | `20` | `20` |
| `val d: {i64: i64} = {1: 10, 2: 20}` | `"{d[2]}"` | `20` | `20` |
| `val d = {1: 10, 2: 20}` | `d[2].to_string()` | **`<value:0x14>`** | `20` |
| `val d = {1: 10, 2: 20}` | `"{d[2]}"` | **`<value:0x14>`** | `20` |

`.to_string()` versus interpolation makes no difference — **the type annotation
does.** The verifying lane's matrix used annotated declarations throughout, so
it measured only the half that works. `0x14` is 20, so the value is stored and
found correctly; it is the read that fails to unbox when the dict type was
inferred.

### Same-family gaps found and deliberately not fixed

1. **Integer dict *values* have the same asymmetry.** `{"a": 8}` gives `1` on
   the JIT against `8` interpreted. Not fixable at the same line: the
   `Dict.get` lowering emits **no `UnboxInt` at all**, so boxing the value would
   turn the accidentally-correct `{"a": 1}` case into `8`. The missing unbox on
   the read path has to land first.
2. **`Dict.insert` is still unrouted** — `Function 'Dict.insert' not found`,
   exit 0. A separate dispatch gap from the `rt_dict_insert` → `rt_dict_set`
   alias.
3. **Interpreter `keys()` order is nondeterministic run to run** — the same
   binary flips `a`/`b`. Any spec asserting key order is flaky.

# Re-measurement — 2026-07-29

Fresh measurement against a binary built from scratch today, after "many fixes
landed" per the task brief (array `index_of`, `first`/`last`/`pop`, `to_upper`,
`strip`, `enumerate`, `parse_int`, `text.lines`, dict integer keys/values,
array-to-string formatting, `Dict.insert`, enum associated fns, plus the
lambda-demotion stopgap `8b72b34f005` — "fix(jit): refuse to compile
lambda-containing modules -- the closure ABI is wrong"). Same 60-probe corpus,
same probe names, so this diffs cleanly against both prior sections.

## Binary under test

| | |
|---|---|
| Command | `cd src/compiler_rust && cargo build -p simple-driver` |
| Binary | `/home/ormastes/dev/pub/simple/src/compiler_rust/target/debug/simple` |
| mtime | **2026-07-29 02:55:53.500 +0000** |
| Size | 481,205,552 bytes |

`src/compiler_rust/` has heavy concurrent edits from other sessions (the build
itself blocked briefly on another session's cargo lock; a stray `nohup` build
was killed and restarted cleanly). The binary above is the artifact every probe
in this section actually ran against — driver invocation:

```sh
ROOT=/home/ormastes/dev/pub/simple
PROBE_BIN=$ROOT/src/compiler_rust/target/debug/simple \
PROBE_OUTDIR=$ROOT/build/probe_divergence/fast_0729 \
PROBE_RESULTS=$ROOT/build/probe_divergence/fast_results_0729.tsv \
  sh build/probe_divergence/fast_driver.shs
```

`fast_driver.shs` still works unmodified — it already takes `PROBE_BIN` (fixed
in the prior re-measurement) and already tags a bailout-detected value with
`<via-jit-bailout>` in its own output, which is what caught the four
lambda-demotion probes below without any extra scripting.

## JIT-compiled vs demoted — `SIMPLE_JIT_TRACE_ADDR=1` audit

Per the task's method rule, every probe was re-run a second time with
`SIMPLE_EXECUTION_MODE=jit SIMPLE_JIT_TRACE_ADDR=1` to check for a `[jit-addr]`
line (real Cranelift compile) versus its absence (demotion to the interpreter,
whether or not it also printed `JIT compilation failed`).

**56 of 60 probes show `[jit-addr] probe_all ...` and `[jit-addr] main ...`** —
real JIT compiles, including `dict_get_or_present`, `dict_get_or_absent`,
`dict_insert_then_keys`, `text_lines_len`, and `text_parse_int` (all
independently confirmed with the marker present).

**4 probes have no `[jit-addr]` marker at all: `arr_map`, `arr_filter`,
`arr_any`, `arr_all`.** These are exactly the lambda-taking probes, and they
match the `<via-jit-bailout>` tag `fast_driver.shs` already attached from
grepping `JIT compilation failed` in their logs. This is the
`8b72b34f005` stopgap guard working as designed: the whole module demotes to
the interpreter rather than miscompiling the closure ABI. **They are AGREE, but
AGREE-via-demotion — the JIT never ran on these four, so the JIT builtin itself
remains unverified for `map`/`filter`/`any`/`all`.**

## Totals

| Verdict | 07-28 orig | 07-28 re-measured | **07-29 (this run)** | Δ vs 07-28 re-measured |
|---|---|---|---|---|
| AGREE (table verdict) | 31 | 51 | **58** | +7 |
| — of which AGREE-via-demotion (not real JIT) | 0 | 0 (arr_map/filter/any/all were DISAGREE then) | **4** | +4 |
| — of which AGREE-on-actual-JIT | 31 | 51 | **54** | +3 |
| DISAGREE | 18 | 9 | **2** | −7 |
| UNMEASURED on JIT | 11 | 0 | **0** | 0 |

By receiver: array **0 DISAGREE / 27** (4 AGREE-via-demotion), dict **2
DISAGREE / 11**, text **0 DISAGREE / 22**.

## Full table

| Probe | Recv | JIT (`run`) | Interp (`test`) | Verdict |
|---|---|---|---|---|
| `arr_len` | array | `3` | `3` | AGREE |
| `arr_index_of_first` | array | `0` | `0` | AGREE |
| `arr_index_of_mid` | array | `1` | `1` | AGREE |
| `arr_index_of_last` | array | `2` | `2` | AGREE |
| `arr_index_of_absent` | array | `-1` | `-1` | AGREE |
| `arr_index_of_empty` | array | `-1` | `-1` | AGREE |
| `arr_index_of_text` | array | `2` | `2` | AGREE |
| `arr_contains_yes` | array | `true` | `true` | AGREE |
| `arr_contains_no` | array | `false` | `false` | AGREE |
| `arr_contains_text` | array | `true` | `true` | AGREE |
| `arr_push_len` | array | `3` | `3` | AGREE |
| `arr_push_last` | array | `3` | `3` | AGREE |
| `arr_enumerate_len` | array | `3` | `3` | AGREE |
| `arr_index0` | array | `10` | `10` | AGREE |
| `arr_index_last` | array | `30` | `30` | AGREE |
| `arr_first` | array | `10` | `10` | AGREE |
| `arr_last` | array | `30` | `30` | AGREE |
| `arr_pop` | array | `3` | `3` | AGREE |
| `arr_reverse` | array | `30` | `30` | AGREE |
| `arr_sort` | array | `10` | `10` | AGREE |
| `arr_join` | array | `a-b` | `a-b` | AGREE |
| `arr_slice` | array | `2` | `2` | AGREE |
| `arr_is_empty` | array | `true` | `true` | AGREE |
| `arr_map` | array | `2` (`<via-jit-bailout>`, no `[jit-addr]`) | `2` | AGREE-via-demotion |
| `arr_filter` | array | `2` (`<via-jit-bailout>`, no `[jit-addr]`) | `2` | AGREE-via-demotion |
| `arr_any` | array | `true` (`<via-jit-bailout>`, no `[jit-addr]`) | `true` | AGREE-via-demotion |
| `arr_all` | array | `true` (`<via-jit-bailout>`, no `[jit-addr]`) | `true` | AGREE-via-demotion |
| `dict_keys_len` | dict | `2` | `2` | AGREE |
| `dict_values_len` | dict | `2` | `2` | AGREE |
| `dict_contains_key_yes` | dict | `true` | `true` | AGREE |
| `dict_contains_key_no` | dict | `false` | `false` | AGREE |
| `dict_get_or_present` | dict | `error` (stderr `Runtime error: Function 'Dict.get_or' not found`, exit 0, `[jit-addr]` present) | `1` | **DISAGREE** |
| `dict_get_or_absent` | dict | `error` (stderr `Runtime error: Function 'Dict.get_or' not found`, exit 0, `[jit-addr]` present) | `-7` | **DISAGREE** |
| `dict_index_read` | dict | `2` | `2` | AGREE |
| `dict_len` | dict | `2` | `2` | AGREE |
| `dict_insert_then_keys` | dict | `2` | `2` | AGREE |
| `dict_index_write` | dict | `2` | `2` | AGREE |
| `dict_get` | dict | `1` | `1` | AGREE |
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
| `text_strip` | text | `pad` | `pad` | AGREE |
| `text_to_upper` | text | `HELLO` | `HELLO` | AGREE |
| `text_to_lower` | text | `abc` | `abc` | AGREE |
| `text_char_code_at` | text | `104` | `104` | AGREE |
| `text_lines_len` | text | `3` | `3` | AGREE |
| `text_char_at` | text | `e` | `e` | AGREE |
| `text_find_str` | text | `2` | `2` | AGREE |
| `text_rfind` | text | `3` | `3` | AGREE |
| `text_parse_int` | text | `42` | `42` | AGREE |
| `text_to_string` | text | `hi` | `hi` | AGREE |

## (a) Newly-AGREE since the 2026-07-28 re-measurement — 7 probes

| Probe | Was (07-28 re-measured) | Now | Mechanism |
|---|---|---|---|
| `arr_map` | DISAGREE (`3` wrong value, exit 0) | AGREE-via-demotion | lambda-demotion guard `8b72b34f005`; JIT never compiles it |
| `arr_filter` | DISAGREE (`0`, silent wrong value) | AGREE-via-demotion | same |
| `arr_any` | DISAGREE (`nil`) | AGREE-via-demotion | same |
| `arr_all` | DISAGREE (`nil`) | AGREE-via-demotion | same |
| `dict_insert_then_keys` | DISAGREE (`1`, `Dict.insert` not found) | **AGREE (real JIT fix)** | `Dict.insert` dispatch landed; `[jit-addr]` confirmed |
| `text_lines_len` | DISAGREE (`-1`, `str.lines` not found) | **AGREE (real JIT fix)** | `text.lines` landed; `[jit-addr]` confirmed |
| `text_parse_int` | DISAGREE (float-formatted `0`) | **AGREE (real JIT fix)** | `parse_int` fix landed; `[jit-addr]` confirmed |

Only 3 of these 7 (`dict_insert_then_keys`, `text_lines_len`, `text_parse_int`)
are confirmed fixes on the JIT itself. The other 4 (`arr_map/filter/any/all`)
read as fixed in the verdict column but are masked by demotion, not fixed in
the JIT builtin dispatch — see the audit above.

## (b) Still DISAGREE — 2 probes

| Probe | JIT | Interp | Note |
|---|---|---|---|
| `dict_get_or_present` | `error` | `1` | `Dict.get_or` still unrouted; `[jit-addr]` confirms the JIT compiled the module and hit a missing-function runtime error, exit 0 — this is the task's known-still-open item, confirmed present |
| `dict_get_or_absent` | `error` | `-7` | same missing symbol, `Dict.get_or` |

Both are the same root cause as the fixed `Dict.insert` case in (a): a missing
dispatch arm, not a compile failure. `Dict.get_or` is the one remaining unrouted
`Dict.*` method in this corpus.

## (c) Newly DISAGREE — 0 probes (no regression found)

Checked deliberately, per the task brief. Every probe in the 07-28 re-measured
AGREE set (51 probes) is still AGREE today; the two 07-29 DISAGREE probes
(`dict_get_or_present`, `dict_get_or_absent`) were **already** DISAGREE in the
07-28 re-measurement, not new. **Zero `AGREE → DISAGREE` transitions.** No
regression to report for this run.

## Artifacts

| | |
|---|---|
| Results TSV | `build/probe_divergence/fast_results_0729.tsv` |
| Per-probe logs (value capture) | `build/probe_divergence/fast_0729/{j,i}_<name>.log` |
| Per-probe logs (`[jit-addr]` audit, `SIMPLE_JIT_TRACE_ADDR=1`) | `build/probe_divergence/jit_trace_0729/j_<name>.log` |
| Corpus | `build/probe_divergence/cases.txt` (unchanged, 60 cases) |
| Driver | `build/probe_divergence/fast_driver.shs` (unchanged, still correct) |

All prior sections and artifacts are left in place.
