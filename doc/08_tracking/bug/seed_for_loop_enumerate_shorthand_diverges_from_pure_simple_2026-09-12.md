# The Rust seed's for-loop "enumerate shorthand" diverged from the pure-Simple compiler

- Status: **RESOLVED** (2026-09-12) — fixed and verified in-tree (worktree
  `simple-for-destructure`, branch `work/for-comma-destructure`, based on
  `704719ab79a`). Not committed by this pass; see Verification.
- Found: 2026-09-12, as the lead decision on the "Design conflict" section of
  `doc/08_tracking/bug/dict_items_for_loop_destructure_and_jit_missing_2026-09-12.md`
  (agent G), which this record supersedes for that question.
- Component: Rust seed parser (`parser/src/stmt_parsing/control_flow.rs`
  `parse_for_pattern`, `parser/src/ast/nodes/statements.rs` `ForStmt`),
  seed tree-walk interpreter (`compiler/src/interpreter_control.rs`
  `exec_for_inner` + the `try_exec_*_for_loop` fast paths,
  `compiler/src/interpreter_call/block_execution.rs` two sites,
  `compiler/src/interpreter_helpers/patterns.rs`)
- Lane: seed interpreter (the divergent engine). The seed JIT and the
  pure-Simple compiler already agreed with each other.

## The decision

**A bare comma pattern in a for loop is ALWAYS a tuple destructure, of any
arity, regardless of what the iterable is.** `for a, b in xs:` means exactly
what `for (a, b) in xs:` means. The seed's "enumerate shorthand"
(`for i, x in arr:` → index, item) is **removed**. Enumerate intent is
written `for i, x in arr.enumerate():`.

The seed follows the pure-Simple compiler, never the other way round.

## Why this was the answer, not a coin flip

Three of the four relevant surfaces already implemented the decided rule.
Only the seed's tree-walk interpreter did not.

| engine | `for a,b in [(1,2),(3,4)]` | `for i,x in arr.enumerate()` | `for a,b in [10,20,30]` |
|---|---|---|---|
| pure-Simple compiler | destructure (by construction) | destructure of (i, x) | binds `nil` |
| seed JIT (before this fix) | destructure — `1\|2;3\|4;` | correct — `0\|10;1\|20;2\|30;` | `nil\|nil;` |
| seed interpreter (before) | **enumerate** — `0\|(1,2);` | **double wrap** | enumerate — `0\|10;1\|20;` |
| all three (after) | destructure | correct | binds `nil` |

Pure-Simple's parser (`src/compiler/10.frontend/core/parser_stmts.spl`,
`parse_for_stmt` + `encode_for_tuple_binding`) joins an arbitrary bare name
list into the same `"(a,b,c)"` pattern the parenthesized spelling produces —
**unconditionally, without ever looking at the iterable** — and the HIR
lowering (`src/compiler/20.hir/hir_lowering/statements.spl`, `StmtKind.For`)
emits one `let name = __for_tuple_elem[i]` per name, skipping `_`. There is
no enumerate concept anywhere in that path, and pure-Simple's own source
already uses the bare-comma-over-`.enumerate()` spelling
(`src/compiler/30.types/variance_types.spl:261,476`,
`src/compiler/70.backend/linker/link.spl:290`, and others).

### The non-tuple case: `nil`, not an error

The task brief asked for "a clear runtime error" here, with the caveat *match
the pure-Simple compiler's behaviour if it has one*. It has one, and it is
not an error: the lowering indexes each element, so a non-tuple simply has no
element 0/1 and every name binds `nil`. The seed JIT already answered exactly
that. Two further considerations settled it:

- An interpreter that errors while the JIT binds `nil` cannot be green in
  both lanes without separate JIT codegen work, and lane disagreement is the
  defect this change exists to remove.
- The seed interpreter's third behaviour — `bind_pattern` returning false and
  the loop `continue`ing — was the worst of the options: it skipped every
  iteration in total silence.

Honest cost, recorded rather than glossed: `nil`-binding means a call site
misclassified during the migration produces `nil`s instead of a loud failure.
The regression suite and the census below are the only net. This is a **lead
decision that deviates from the brief's literal wording**, not a footnote.

### Scope note: the PARENTHESIZED spelling changed too

`bind_for_pattern` / `bind_for_pattern_value` replace `bind_pattern` /
`bind_pattern_value` for **every** `Pattern::Tuple` loop pattern, not only
bare-comma ones — which is forced, since the parser now produces one
indistinguishable pattern for both spellings. So `for (a, b) in <non-tuples>:`
went from "skip every iteration in silence" to nil-binding, and
`for (a, b) in <3-tuples>:` went from "skip every iteration" to binding the
first two elements. Both follow directly from the decision (bare ==
parenthesized) and both match pure-Simple's `__for_tuple_elem[i]` lowering,
which has never required arity agreement. Stated explicitly because the
census below covers bare-comma sites only: a parenthesized census would need
element-type analysis of hundreds of sites, and every behaviour it could
change is a change from *silent total skip* to *something*, so there is no
shape that was working before and is broken now.

Measured on both binaries, one probe, both engines:

| shape | baseref interpreter | baseref JIT | candidate (both engines) |
|---|---|---|---|
| `for (a, b) in [10, 20, 30]:` | `` (silent skip, every iteration) | `nnn` | `nnn` |
| `for (p, q) in [(1,2,3), (4,5,6)]:` | `` (silent skip) | `12;45;` | `12;45;` |
| `for i, pr in [(0,(1,2)), (1,(3,4))]:` (nested) | `method to_string not found on type tuple` | `0:12;1:34;` | `0:12;1:34;` |

So the widening is a third interpreter/JIT convergence, not a new risk: every
cell it changed was previously a silent skip or an error in the interpreter
only, and the candidate's answers are byte-identical to what the JIT already
produced.

## Defects fixed

1. **Interpreter index-wrap.** `exec_for_inner` and both `block_execution.rs`
   for-loop executors wrapped each item as `(index, item)` whenever
   `ForStmt.auto_enumerate` was set, unless the iterable was syntactically
   `.items()`/`.entries()` or evaluated to a `Value::Dict` (agent G's static
   predicate, now deleted). Consequence: `for a, b in rows:` over an array of
   pairs enumerated, and `for i, x in arr.enumerate():` **double**-wrapped.
2. **Three-or-more names parsed as an Or pattern.** `parse_for_pattern` read
   the second element with `parse_pattern`, whose comma-or-pattern rule
   swallowed the separator, so `for a, b, c in e:` became
   `Tuple([a, Or([b, c])])`. The interpreter then failed the match and
   skipped **every** iteration in silence; the JIT failed codegen with
   `unresolved identifier 'b'`. Fixed by reading each element after the first
   with `parse_pattern_no_comma_or` — the same helper the struct-pattern field
   list and `parse_enum_payload_patterns` already use for this exact reason.
3. **`_` could not lead a bare comma pattern.** `for _, x in d.items():`
   fell through to `parse_pattern`, which built an Or. Fixed by admitting
   `TokenKind::Underscore` into the first-element fast path.

## Changes (seed only; the pure-Simple compiler needed nothing)

| file | change |
|---|---|
| `parser/src/stmt_parsing/control_flow.rs` | `parse_for_pattern` returns a plain `Pattern`; loops on commas for arbitrary arity; uses `parse_pattern_no_comma_or` per element; admits `_` first. `auto_enumerate` dropped from both call sites and all three `ForStmt` literals. |
| `parser/src/ast/nodes/statements.rs` | `ForStmt::auto_enumerate` deleted. The AST now carries one `Pattern::Tuple` for both spellings, so no later stage can tell them apart. |
| `compiler/src/macro/hygiene.rs`, `macro/substitution.rs`, `interpreter_method/collections.rs` | field copies removed (4 lines). |
| `compiler/src/interpreter_helpers/patterns.rs` | `for_loop_iterable_is_items_or_entries_call` **deleted**. New `for_loop_tuple_elements` + `bind_for_pattern` / `bind_for_pattern_value`: a tuple loop pattern binds element-wise, padding with `Nil`. Two binders, not one, because `bind_pattern_value` carries `val`-binding const bookkeeping that `bind_pattern` does not — collapsing them would have changed const semantics at the block-executor sites. `bind_sequence_pattern` is deliberately untouched: strict arity-and-type matching is correct for a `case` arm, which has a next arm to fall through to. |
| `compiler/src/interpreter_control.rs` | `exec_for_inner` drops the wrap and the predicate, binds via `bind_for_pattern`. `try_exec_enumerated_int_array_for_loop`'s perf fast path re-keyed: its shape matcher now requires the iterable to be a zero-arg `.enumerate()` `MethodCall` over an identifier, and no longer matches a bare `Expr::Identifier` — otherwise the fast path would answer index/item while the general path destructures. The seven other fast paths' `\|\| for_stmt.auto_enumerate` bail-outs were dead code (each one's `parse_*` already requires `parse_for_loop_identifier`, which rejects a tuple pattern) and were removed. |
| `compiler/src/interpreter_call/block_execution.rs` | both for-loop executors bind via `bind_for_pattern_value`. |

JIT/MIR lowering needed **no change**: it never read `auto_enumerate`, and
once the parser emits a flat `Pattern::Tuple` the existing HIR path handles
3-arity correctly (verified: `TRIPLES=123;456;` under JIT).

## Call-site migration

Full census (55 sites, widened regex, decision + reason per site):
`J_census.md` in the lane scratchpad. Summary:

- **53 of 55 LEAVE** — the iterable yields pairs/tuples, so destructure is
  what the code already meant. Five of those (`src/plugins/backend_c/…`,
  `case Struct(fields)` where `fields: [(text, ConstValue)]`,
  `src/compiler/15.blocks/blocks/definition.spl:327`) were **latently wrong**
  under the removed shorthand — they bound `field_name` to the loop index and
  `field_val` to the whole tuple — and are fixed by this change.
- **4 lines MIGRATE** to `.enumerate()`: `test/01_unit/app/interpreter/perf_spec.spl:363,373`
  and its `test/unit/` mirror `:365,375`. These are the
  `try_exec_enumerated_int_array_for_loop` perf pin; they now exercise the
  re-keyed fast path in its correct spelling. Both trees changed together so
  `check-test-tree-divergence` gains no new offender.
- **1 probe rewritten**: `test/01_unit/language/probe_dict_items_for_loop.spl`
  pinned the removed feature; it and its spec now assert destructure in both
  lanes.
- **0 sites in the core-c bootstrap lane** needed `.enumerate()`. Stated
  explicitly because the smoke test's own header notes that lane
  "deliberately does not provide the dynamic `Array.enumerate` method
  symbol"; no migrated site is under `src/runtime/simple_core/**` or a
  noalloc tree.

`.enumerate()` was confirmed present in all five surfaces before being relied
on: seed interpreter (`interpreter_method/collections.rs:477,961`), seed JIT
(`rt_array_enumerate`, `codegen/instr/calls.rs:3738`), Rust runtime
(`runtime/src/value/collections.rs:5576`), C runtime
(`src/runtime/runtime_native.c:14929`), pure-Simple
(`_EvalOps/call_method_eval.spl:1112`, registered at
`30.types/type_system/builtin_registry.spl:132`) and pure-Simple's core
runtime (`src/runtime/simple_core/core_array_query.spl:343`).

Doc: `doc/07_guide/quick_reference/syntax_quick_reference.md` § For Loops —
the shorthand was never documented there (so nothing to unwrite), but the
rule is now stated explicitly alongside an `.enumerate()` example, so it
cannot drift back in by accident.

## Verification

Three binaries, because the deployed seed is **not** a valid attribution
baseline: it predates this worktree's base commit by six days, so a
deployed-seed diff also carries every unrelated change in between (it was,
for example, the entire cause of the one alarming `test/04_smoke`
difference — see below).

| role | path | size | built |
|---|---|---|---|
| deployed seed (context only) | `/home/yoon/dev/simple/bin/release/aarch64-unknown-linux-gnu/simple` | 50,093,192 | 2026-09-06 09:59:11 |
| **base reference** — `704719ab79a` with this change reverted, built here | `…/scratchpad/J/simple_baseref` | 51,188,328 | 2026-09-12 12:08:14 |
| **candidate** | `/home/yoon/dev/simple-for-destructure/src/compiler_rust/target/release/simple` (copy at `…/scratchpad/J/simple_candidate`) | 51,245,672 | 2026-09-12 11:32:41 |

The base reference was produced by reverting the nine modified Rust files,
building, saving the binary, restoring the files and rebuilding — the
rebuild is **byte-identical** to the candidate, so the two binaries differ
by exactly this change and nothing else. The worktree's `bin/simple` symlink
points at the candidate's absolute path.

### RED → GREEN

| pin | base reference | candidate |
|---|---|---|
| `test/04_smoke/compiler_unparenthesized_tuple_for.spl` (interpreter) | `tuple-for-fail=0:(0, aether);1:(1, glass); adjacent=0:aether;1:glass;` | `tuple-for-ok=0:aether;1:glass;` |
| `test/04_smoke/compiler_unparenthesized_tuple_for_runtime.spl` (interpreter) | `tuple-for-fail=0:(0, aether);1:(1, glass);` | `tuple-for-ok=0:aether;1:glass;` |
| both smoke tests (JIT) | already `tuple-for-ok=…` | unchanged |
| `test/01_unit/language/for_bare_comma_destructure_spec.spl` (new) | **0 passed / 8 failed** | **8 passed / 0 failed** |
| `test/01_unit/language/dict_items_for_loop_spec.spl` (G's, pin (a) reversed) | 1 passed / 5 failed | **6 passed / 0 failed** |

The new probe's output is now **byte-identical under both engines**:
`BARE_PAIRS=1|2;3|4;` `PAREN_PAIRS=1|2;3|4;` `ENUM_REPR=0|10;1|20;2|30;`
`ITEMS_TOTAL=6` `ENTRIES_TOTAL=6` `DICT_TOTAL=6` `TRIPLES=123;456;`
`WILD_LEN=3` `NONTUPLE=nil|nil;nil|nil;nil|nil;`

### Migration-touched specs, both binaries

| spec | base reference | candidate |
|---|---|---|
| `test/01_unit/app/interpreter/perf_spec.spl` (migrated to `.enumerate()`) | 41/41 OK | **41/41 OK** |
| `test/unit/app/interpreter/perf_spec.spl` (mirror, migrated) | 41/41 OK | **41/41 OK** |

The perf pin passing on BOTH binaries is the point: the `.enumerate()`
spelling is correct under the old shorthand too (it summed positions either
way), so migrating it did not weaken it, and the re-keyed
`try_exec_enumerated_int_array_for_loop` fast path still admits it.

### The perf fast path really is reached (mechanism, not just correctness)

`perf_spec` passing 41/41 proves the sums are right; it does not prove
`try_exec_enumerated_int_array_for_loop` still fires. A re-keyed matcher that
silently never matched would pass that spec while demoting every enumerate
loop to the general path. Measured directly, interpreter lane, the exact
`perf_spec` shape (`val data = [1; N]`, single-statement body
`sum = sum + enum_idx`):

| binary | spelling | n=200,000 | n=800,000 |
|---|---|---|---|
| candidate | `data.enumerate()` | 0.38s | **0.64s** |
| candidate | same + a second body statement (breaks the shape on purpose) | 1.37s | **5.31s** |
| base reference | `data` (the old bare shorthand) | — | 0.35s |
| base reference | `data.enumerate()` | — | **4.06s** |

Reading: on the candidate the `.enumerate()` spelling is flat in `n` (0.38 ->
0.64 for 4x the elements, i.e. startup-dominated) while the deliberately
broken shape scales linearly (1.37 -> 5.31, ratio 3.9) — the fast path fires
for one and not the other. On the base reference the fast path fired only for
the bare spelling (0.35s) and NOT for `.enumerate()` (4.06s, 12x slower),
because its matcher required a bare `Expr::Identifier` iterable. The pin
therefore did not merely survive the migration — **migrating `perf_spec` was
necessary for it to keep meaning anything**, since the `.enumerate()` form it
now uses was the slow path before this change.

### Regression suites, base reference vs candidate, same command

| suite | base reference | candidate |
|---|---|---|
| `test/01_unit/language` | 167 total, 144 passed, 23 failed | 167 total, **159 passed, 8 failed** |
| `test/01_unit/app/interpreter` | 147 total, 141 passed, 6 failed | 147 total, 140 passed, 7 failed |
| `test/01_unit/interpreter` (2 specs, re-run serially — the parallel run's totals disagreed) | 8/8 passed | **8/8 passed** |
| `test/04_smoke` (9 files × 2 engines, output-hash diff) | — | **16 SAME, 2 intended DIFF** (the tuple-for pair, interpreter lane) |

Per-spec verdict diffs surfaced four apparent OK→ERROR flips —
`array_repeat_spec`, `in_operator_membership_spec`, `class_method_call_spec`,
`chained_call_receiver_mutation_spec`. **All four are load flakes, not
regressions**: re-run serially, every one is OK on BOTH binaries
(5/5, 20/20, 1/1, 5/5 respectively). The tell was the symmetry — the same
runs showed equal-and-opposite ERROR→OK flips on sibling specs
(`array_index_of_spec`, `chained_call_self_slot_corruption_spec`) that this
change cannot plausibly have fixed. The host was running several suites in
parallel under heavy load. **No spec passes on the base reference and fails
on the candidate.**

`test/04_smoke/net_tcp_facade_jit_probe.spl` was excluded from the hash diff
and checked separately: it blocks on a real `accept()` and times out
**identically on both binaries**. Against the *deployed seed* it looked like
a dramatic change (seed: `Function 'nil.local_addr' not found`; candidate:
`PASS bind -> kernel-assigned 127.0.0.1:46033` then hang) — which is exactly
the artefact that motivated building a proper base reference. None of it is
attributable to this change.

### cargo

- `-p simple-compiler --lib` filtered to the touched modules
  (`interpreter_helpers::`, `interpreter_control::`, `mir::lower::`,
  `patterns`): **560 passed, 0 failed**.
- `-p simple-parser`: 454 passed, 1 failed —
  `ts_arrow_detection_rule_was_retired_when_the_arrow_lambda_landed`, which
  calls `simple_parser::error_recovery::detect_common_mistake` directly with
  two literal tokens. `error_recovery.rs` is untouched by this change
  (`git status` confirms), so the verdict cannot depend on it: pre-existing.
- `-p simple-compiler --lib` full: 3999 passed, 15 failed, all in
  `pipeline::native_project`, `linker::native_binary`, and
  `interpreter_extern::vulkan`. Re-run with `--test-threads=1`,
  `pipeline::native_project::tests::test_struct_receiver_guard_native_contract`
  **passes** — it was a `PoisonError` cascade victim — while the vulkan and
  linker ones fail independently and are environment-dependent (no Vulkan
  runtime; a C-compiler-default assertion). None is reachable from a
  for-loop pattern change.

## Left open

- The 15 `-p simple-compiler --lib` failures are argued pre-existing from
  module locality plus the isolation re-run above; they were not re-run
  against the base-reference *build*.
- `test/01_unit/lib/common` (1082 specs) and `test/02_integration/app` (300
  specs) are long runs that had not finished when this record was written.
  They are progressing on both binaries from the same stable binary copies
  (so subprocess probes are clean too), and the running per-file comparison
  at the last check was:

  | suite | files compared on BOTH | candidate worse | candidate better |
  |---|---|---|---|
  | `test/01_unit/lib/common` | 405 | **0** | 3 |
  | `test/02_integration/app` | 167 | **0** (3 apparent, all disproved) | 2 |

  The three `test/02_integration/app` flips
  (`coverage_log_modes_spec`, `todo_scan_log_modes_spec`,
  `llm_process/llm_process_gen_spec`) were each re-run serially and are
  **4/4, 4/4 and 14/14 OK on BOTH binaries** — subprocess-spawning specs,
  timing-sensitive under the parallel load. Recipe to finish the comparison
  from the raw logs (`…/scratchpad/J/{baseref,cand2}_test_<suite>.txt`):

  ```sh
  for t in 01_unit_lib_common 02_integration_app; do
    for b in baseref cand2; do
      grep -oE '^\s*(PASS|FAIL)\s+\S+\.spl' "$S/${b}_test_$t.txt" \
        | awk '{print $2, $1}' | sort -u > "$S/p_${b}_$t.txt"
    done
    join "$S/p_baseref_$t.txt" "$S/p_cand2_$t.txt" \
      | awk '$2=="PASS" && $3=="FAIL" {print "REGRESSION", $1}'
  done
  ```

  Any hit must be re-run **serially on both binaries** before being believed;
  every apparent flip in this lane so far has been a load flake.
- `nil.to_string()` is an unrelated pre-existing engine divergence: the JIT
  renders `"nil"`, the interpreter raises `method to_string not found on type
  nil`. The new probe deliberately reports its `nil` pin via `== nil` so a
  for-loop spec does not fail for that reason. Not filed separately here.
- `for k, v in frozen_dict:` — agent G recorded `Value::FrozenDict` as a
  pre-existing gap in the old runtime check. That check is gone, so the shape
  now follows the same destructure rule as everything else via `iter_to_vec`;
  not separately pinned by a spec.
