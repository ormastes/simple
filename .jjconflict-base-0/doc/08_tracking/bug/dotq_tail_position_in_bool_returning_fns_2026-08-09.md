# BUG: `.?` in tail position of `-> bool` functions leaks the payload (42 sites)

- **Filed:** 2026-08-09
- **Lane:** G4 (NILQ follow-on)
- **Severity:** High — 16 sites return a wrong value; the rest are accidentally correct
- Status: FIXED
- Status re-verified 2026-08-17 by source inspection (triage shard 01).
- **Companions:** `dotq_existence_check_is_scalar_truthiness_on_jit_2026-07-27.md`,
  `dotq_zero_test_hazard_call_sites_2026-07-27.md`,
  `dot_question_truthy_op_returns_payload_as_call_arg_2026-07-20.md`

## Ruling: `.?` returns `T?`, not `bool`. The call sites are wrong.

This was investigated as a possible operator-semantics mismatch. It is not one —
the specification is explicit and the interpreter matches it.

`doc/07_guide/quick_reference/syntax_quick_reference.md:548`:

> ### Existence Check (`.?`) — Returns `T?`
> The `.?` operator checks if a value is **present** (not nil AND not empty).

with the per-type table at L566-571 (`list.?` → `Some(list)` if non-empty, `nil`
if `[]`; `str.?` → `Some(str)` if non-empty, `nil` if `""`).

`src/compiler/10.frontend/core/interpreter/eval.spl:436-444` (`EXPR_EXISTS_CHECK`)
evaluates the base, normalizes the option binding, and returns the **payload** if
present else `nil`. That is exactly the specified behaviour. **eval.spl needs no
change.** There is no one-line compiler fix that repairs the 42 sites, because the
compiler is not what is broken.

`.claude/rules/language.md`'s "Use `.?` over `is_*` predicates" is an *idiom*
recommendation for guard/binding position (`if val x = opt.?:`), not a claim that
`.?` evaluates to `bool`. Authors read it as the latter. That misreading is the
root cause of all 42 sites, and the rules file should be clarified.

## Execution evidence (2026-08-09)

Probe: `fn tail_dotq(xs: [text]) -> bool: xs.?`

| engine | `tail_dotq(["x","y"])` | `tail_dotq([])` |
|---|---|---|
| interpreter (`SIMPLE_EXECUTION_MODE=interpreter`) | returns the **array** `[x, y]` — `error: semantic: method to_text not found on type array (receiver value: [x, y])` | `nil` |
| Rust seed / default JIT | `true` | **`true`** — WRONG, empty list is falsy per spec |

Two independent defects are visible here:
1. **Interpreter:** the payload escapes a `-> bool` function completely unconverted.
2. **Seed/JIT:** collapses to scalar truthiness *and* gets the empty-list case
   wrong (returns `true` for `[]`). This is the already-filed
   `dotq_existence_check_is_scalar_truthiness_on_jit_2026-07-27` defect; the
   empty-container zero-test miss is a new datum for it.

Note the engines **disagree** on every one of these sites.

## The 42 sites (owned `src/**` + `test/**`, vendored and `build/` copies excluded)

`accidentally-correct: 26` — receiver is `Option<struct/handle>`, so payload is
always a non-null pointer and `nil` is falsy; behaves identically to a predicate
under truthiness on both engines. Not urgent, still non-conforming.

`genuinely-wrong: 16` — receiver can legitimately be `0`, `false`, or empty, or
the result is consumed where a real `bool` is required:

| File:line | fn | tail expr | receiver |
|---|---|---|---|
| src/compiler/00.common/effects_cache.spl:54 | `has_violations` | `self.violations.?` | `[text]` |
| src/compiler/35.semantics/verification_checker.spl:142 | `has_violations` | `self.violations.?` | `[VerificationViolation]` |
| src/compiler/20.hir/inference/infer.spl:214 | `has_errors` | `self.errors.?` | `[InferError]` |
| src/compiler/30.types/type_system/checker.spl:276 | `has_errors` | `self.errors.?` | `[TypeError]` |
| src/compiler/40.mono/monomorphize/binding_specializer.spl:39 | `has_bindings` | `self.bindings.?` | `{text: text}` |
| src/app/package.registry/auth.spl:37 | `save_credentials` | `write_result.ok.?` | `bool` payload |
| src/lib/nogc_sync_mut/src/db.spl:152 | `save` | `write_result.ok.?` | `bool` payload |
| src/app/interpreter/core/symbol.spl:118 | `contains` | `self.map[s].?` | `SymbolId?` (id 0) |
| src/lib/nogc_sync_mut/conf.spl:69 | `conf_has` | `c.entries.get(key).?` | `text?` (empty value) |
| src/app/interpreter/collections/persistent_dict/dict.spl:73 | `contains` | `self.get(key).?` | generic `V?` |
| src/lib/nogc_async_mut/actor/mailbox.spl:45 | `expects_reply` | `self.reply_id.?` | `i64?` (id 0) |
| test/02_integration/storage/dbfs/dbfs_engine_btree_delete_rebalance_spec.spl:35 (+ `test/integration/` twin) | `has` | `result.?` | `text?` |
| test/02_integration/app/app_mcp_intensive_spec.spl:521 (+ 2 twins) | `validate_mcp_response` | `response.get("jsonrpc").? and response.get("id").?` | `any?` (id may be 0) |

The five `has_errors`/`has_violations`/`has_bindings` compiler sites are the most
serious: on the seed they return `true` for an **empty** error list, so
"did this phase produce errors?" answers yes when it produced none.

## Recommended fix (call sites, not the operator)

Per site, replace the tail `x.?` with an explicit boolean:
`x.? != nil`, or for containers the direct predicate (`not xs.is_empty()`,
`xs.len() > 0`). Do **not** rewrite `.?` guard-position uses — those are correct
idiom. Do **not** change `EXPR_EXISTS_CHECK`.

Ordering: fix the 5 compiler sites first (they gate diagnostics), then the 11
lib/app/test sites, then sweep the 26 accidentally-correct ones for conformance.

## Why this was never caught

Declared return types are not enforced — see
`declared_return_type_not_enforced_2026-08-09.md`. Every one of these 42 functions
returns a non-`bool` from a `-> bool` signature with no diagnostic from any engine.

## Fix landed 2026-08-10 (stream J1)

All 16 genuinely-wrong sites replaced with explicit predicates. `EXPR_EXISTS_CHECK`
untouched, guard-position `.?` untouched.

| site | fix |
|---|---|
| effects_cache.spl:54 `has_violations` | `not self.violations.is_empty()` |
| verification_checker.spl:142 `has_violations` | `not self.violations.is_empty()` |
| infer.spl:214 `has_errors` | `not self.errors.is_empty()` |
| checker.spl:276 `has_errors` | `not self.errors.is_empty()` |
| binding_specializer.spl:39 `has_bindings` | `self.bindings.len() > 0` |
| package.registry/auth.spl:44 | `write_result.ok` (already a bool field) |
| nogc_sync_mut/src/db.spl:165 | `write_result.ok` |
| interpreter/core/symbol.spl:118 `contains` | `self.map.has(s)` |
| nogc_sync_mut/conf.spl:69 `conf_has` | `c.entries.has(key)` |
| persistent_dict/dict.spl:73 `contains` | `self.get(key) != nil` |
| actor/mailbox.spl:45 `expects_reply` | `self.reply_id != nil` |
| dbfs_engine_btree_delete_rebalance_spec.spl:37 `has` (+ `test/integration/` twin) | `result != nil` |
| app_mcp_intensive_spec.spl:521 `validate_mcp_response` (+ 2 twins) | `response.get("jsonrpc") != nil and response.get("id") != nil` |

`!= nil` was chosen over `.? != nil` for the Option sites specifically because it
is the only form that keeps a **zero/empty payload** present: probe on
`src/compiler_rust/target/bootstrap/simple` (33,653,056 bytes, mtime Aug 9 23:10),
identical on the seed/JIT and `SIMPLE_EXECUTION_MODE=interpreter`:

```
has_a=true has_b=true has_z=false            # Dict.has, "a" maps to ""
i64 Some0=true nil=false Some5=true          # Some(0) is PRESENT
txt SomeEmpty=true nil=false SomeX=true      # Some("") is PRESENT
```

Under the old `.?` both `Some(0)` and `Some("")` read as absent — that was the
`mailbox.expects_reply` (reply id 0) and `conf_has` (empty value) hazard.

### Regression spec

`test/01_unit/compiler/diagnostic_predicate_empty_state_spec.spl` — 6 cases over
the real `CachedFunctionEffectInfo`, `VerificationChecker` and `BindingSpecializer`,
pinning empty-state to `false` and populated-state to `true`.

- seed/JIT: `executed=6 passed=6 failed=0`
- interpreter: `executed=6 passed=6 failed=0`
- **sabotage** (three helpers reverted to bare `.?`): `passed=0 failed=6` on
  **both** engines. The spec is not a no-op.

### Side effect worth recording

`dbfs_engine_btree_delete_rebalance_spec.spl` went **0/11 -> 6/11** on the seed.
Its `has()` helper previously returned a truthy payload for every lookup, so the
spec could never distinguish present from absent. The 5 residual failures are
real BTree delete/rebalance defects that the broken predicate had been masking;
they are pre-existing and out of scope for this fix.
