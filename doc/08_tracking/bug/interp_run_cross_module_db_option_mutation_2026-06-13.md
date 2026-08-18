# BUG: `bin/simple run` (interpreter) loses cross-module DB Option/struct returns + field mutations

Status: OPEN (P1)
Status re-verified 2026-08-17 by source inspection (triage shard 02).

- **ID:** `interp_run_cross_module_db_option_mutation`
- **Severity:** P1 (db unusable from a cross-module interpreter `run` driver; works in compiled `test`)
- **Found:** 2026-06-13, perf-umbrella db benchmark driver (AC-5 emit).
- **Distinct from** `interp_unit_param_keyword_collision` (the `unit` keyword bug — already fixed).
  Related to memory `feedback_cross_module_mutation_loss` ("free fn(self: Class) across modules
  loses field mutations; use me-methods + extension impl").

## Symptom
Driving the pure-Simple DB from a separate-module `fn main()` via `bin/simple run`:
- `PureDatabase.memory()` / `open_deferred()` struct/Option return resolves as `None`/empty in the
  caller module → `.unwrap()` panics (ram + persistent configs).
- `MvccTable.insert()` + `mgr.commit()` mutations are silently lost across the module boundary →
  `count_visible()` returns 0 instead of N (wal config).
The SAME db spec passes 13/13 under `bin/simple test` (compiled mode).

## Impact
- AC-5 db benchmark emission (`db_bench_driver.spl`) omits all three mode rows in interpreter
  `run` mode (honest omission, reasons printed — no fabricated numbers). The db spec's correctness
  assertions still pass in compiled `test` mode.

## Repro
`bin/simple run test/05_perf/db/db_bench_driver.spl` → all rows omitted with printed reasons.
Minimal: a 2-module program where module B calls `PureDatabase.memory()` from module A and inserts.

## Proposed next step (staged)
1. Minimal 2-module repro under `test/fixtures/` (Option return + self-mutation across modules).
2. Locate: interpreter executor cross-module value/Option boxing + receiver-mutation handling
   (likely Rust seed — confirm; if seed, scope a change like the `unit` fix).
3. Workaround meanwhile: emit db benchmark numbers from compiled (`test`/smf/native) mode, or keep
   db construction + use in one module.

## Root cause (CONFIRMED)
NOT cross-module, NOT enum-specific, NOT an Option/struct-return or receiver-mutation
boxing problem (the original framing was a red herring — a minimal cross-module
Option/struct-return + me-method mutation repro passed cleanly).

The real bug: the interpreter's `==` / `!=` (and `is`) operators compared the bare
`nil` literal and an `Option::None` value as **unequal**, because they have distinct
runtime representations:
- the `nil` literal evaluates to `Value::Nil`;
- a function declared `-> T?` that does `return nil` yields `Value::Enum { enum_name:
  "Option", variant: "None" }` (an `Option::None`).

So `if opt != nil:` was wrongly **true** when `opt` was a returned `Option::None`,
and the following `opt.unwrap()` then correctly saw None and panicked
`called unwrap on None`. In the db path this fires in `sql_parser._keyword_kind`
(returns `SqlTokenKind?`): for a non-keyword identifier like `bench` it returns nil,
but `if kw != nil:` passed and `kw.unwrap()` panicked — aborting `sql_tokenize` →
`sql_parse` → `exec` → `exec_sql` → the workload's first `db.exec_sql(...)`.

JIT was already correct (it normalizes None/nil); the db path only hits the
interpreter because its `var`-on-shared-pointer code fails JIT lowering (W1003) and
falls back to the interpreter. The W1003 fallback is a separate, out-of-scope issue.

## Fix
`src/compiler_rust/compiler/src/value.rs` — new `Value::is_nil_like()` (true for
`Value::Nil` and `Option::None`; false for `Some(_)`, `Result::Ok/Err`, and all
other values).
`src/compiler_rust/compiler/src/interpreter/expr/ops.rs` — `BinOp::Eq`, `BinOp::NotEq`,
`BinOp::Is` arms: when either operand is nil-like, the result is `both nil-like`
(checked before the `__eq__`/`__ne__` overload dispatch so a user enum's operator
can't shadow nil semantics).

Regression fixture: `test/fixtures/interp_nil_option/nil_option_eq.spl`.

## Verification
- `SIMPLE_EXECUTION_MODE=interpret simple run test/05_perf/db/db_smf_workload.spl`
  → `RESULT|db_ram_insert100|<us>|50` (the `==50` oracle passes; previously panicked).
- Default JIT mode: same RESULT row.
- Fixture passes interpreter + JIT; nil/Some/Result/int/str vs nil all behave;
  `cargo test -p simple-compiler --lib ops::` 34/34.

## Status
FIXED 2026-06-14 — interpreter `==`/`!=`/`is` now bridge the `nil` literal and
`Option::None`. db RAM-insert workload runs in interpreter/script mode.


## 2026-08-17 CORE-P1 triage: UNPROVEN -- fix present in source, could not be executed

Same status and same evidence as `interp_crossmod_local_slot_aliasing_2026-06-15.md` -- these two are the same COW-write-back family. The fix (`merge_shared_collection_fields`, `src/compiler_rust/compiler/src/interpreter_call/core/function_exec.rs:975`, called :1140, from `d8951833a74` + `fb065e87ab5`) is present in current source and carries Array/Dict/ByteArray fields callee->caller, recursing through nested `Value::Object`.\n\nNOT VERIFIED. The deployed `bin/simple` is a Rust seed from 2026-08-16 22:59, predating that fix, so any RED it produces is a stale-binary artifact; an isolated cargo rebuild did not finish under a host load average of 302-361. **Already-fixed CANDIDATE, UNPROVEN.** Note the doc also records that the compiled path already worked, so what is being closed is an interpreter-only divergence -- which is exactly what this fix addresses.


### 2026-08-18 update: DID NOT REPRODUCE against a binary containing the fix

The UNPROVEN status recorded above is now resolved. An isolated `cargo build
--release --bin simple` (own CARGO_TARGET_DIR) completed with rc 0 against a tree
containing `fb065e87ab5`, and the cross-module fixture was re-run A/B:

```
helper.spl:  struct Box: items: [i64]   /  fn fill(b: Box): b.items.push(7)
main.spl:    val b = helper.Box(items: []); helper.fill(b); print len of b.items
```

| binary | result |
|---|---|
| deployed seed (mtime 2026-08-16 22:59, predates fix) | rc 0, `len=1` |
| fresh build containing `fb065e87ab5` | rc 0, `len=1` |

Both are CORRECT (`len=1`), so the row does not reproduce. Engine was verified
rather than assumed: both runs print `[INFO] JIT compilation failed, falling back
to interpreter`, so the INTERPRETER executed the fixture -- which is precisely the
lane this bug is about. A green here is therefore not a JIT-covered false pass.

TWO HONEST CAVEATS, because the evidence is weaker than a clean A/B looks:

1. The very first run of this same fixture against the same deployed seed printed
   `len=0`; a later run of the same binary on the same fixture printed `len=1`.
   The old-seed RED was NOT reproducible run-to-run, and that flip is unexplained
   (HEAD moved deac32e -> 82cd8ee under the session while ~8 peer lanes landed,
   but this fixture exercises the Rust interpreter, not live `.spl` source, so
   that does not obviously account for it). Treat the original RED as unreliable.
2. Because the pre-fix binary also passes, this A/B does NOT isolate
   `merge_shared_collection_fields` as the thing that fixed it. What is
   established is only that the reported defect is absent from current HEAD, not
   which change removed it.
