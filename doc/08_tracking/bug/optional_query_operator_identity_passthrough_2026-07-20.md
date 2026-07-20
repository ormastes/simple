# Interpreter: `.?` operator is an identity pass-through, not a bool conversion

**Date:** 2026-07-20
**Severity:** high (silently wrong boolean result; `.?` is the prescribed
idiom per `.claude/rules/language.md`: "Use `.?` over `is_*` predicates")
**Status:** open
**Found by:** whole-suite triage campaign, `test/feature/plugin/` cluster
(`plugin_startup_block_spec.spl` / `runtime_api_plugin_spec.spl` /
`sugar_plugin_spec.spl`)

## Symptom

`x.?` is documented/expected to evaluate to a `bool` (`true` if `x` is
non-nil, `false` if `x` is nil). On the deployed self-hosted binary
(`bin/release/x86_64-unknown-linux-gnu/simple`), `.?` instead returns `x`
itself unchanged — it is an identity pass-through, not a boolean conversion.

Minimal repro (`bin/simple run`, both untyped-inferred and explicitly
`Thing?`-typed function returns tested, same result either way):

```simple
class Thing:
    x: i64

var _items: [Thing] = []

fn find_it(name_check: bool) -> Thing?:
    for t in _items:
        if name_check:
            return t
    nil

_items = _items + [Thing(x: 42)]

val found_yes = find_it(true)
print "found_yes.? = {found_yes.?}"   # prints "Thing(x: 42)", expected "true"

val found_no = find_it(false)
print "found_no.? = {found_no.?}"     # prints "nil", expected "false"
```

Output:
```
found_yes.? = Thing(x: 42)
found_no.? = nil
```

Confirmed scale-independent (reproduces at N=1) and evaluator-independent so
far (same result under `bin/simple run`; the originating spec failures were
observed under `bin/simple test`) — unlike the related
`bug_sspec_daemon_optional_lookup_equality_divergence_2026-07-20.md` defect,
which is specifically a `test`-daemon-vs-`run` divergence keyed on collection
scale (~20-30 elements) and involves `== nil` comparison, not `.?`. Also
distinct from `interp_dict_in_struct_copy_corruption_2026-07-03.md` (Dict
embedded in a struct losing/corrupting values under copy semantics) — this
defect reproduces with a plain local `var`/`val` binding, no struct-Dict
involved.

## Affected spec

`test/feature/plugin/sugar_plugin_spec.spl` — 4 of 13 examples fail as a
direct result (left unmodified per the "never weaken an assertion" rule; all
four assertions are the officially-prescribed `.?` idiom and are correct as
written):

- "unregister_desugar_rule removes rule — lookup_rule returns nil"
  (`expect(found.?).to_equal(false)` sees `nil`, not `false`)
- "perf_sugar_002_gemm_add rule registers successfully"
  (`expect(found.?).to_equal(true)` sees the `DesugarRule` struct itself, not
  `true`)
- "WFFI f64 carve-out resolved; current rule still uses pointer/i64 args"
  (same shape)
- "FR-PLUG-0003: rule with ast_rewrite_fn=0 registers and lookup returns
  same sentinel" (same shape)

## Root-cause hypothesis

`lookup_rule(name)` (and the repro's `find_it`) return either a real
value/struct or bare `nil` from different branches of a `for`/`if` — the
classic "loop, return match, fall through to nil" idiom the language
encourages `.?` for. The interpreter's `.?` postfix operator appears to not
be wired up as a genuine nil-check-and-convert; it looks through as a no-op
on whatever the underlying value already is. Needs an interpreter-side fix
(not a `.spl`-source fix — every place using `.?` on this idiom is correct
code); out of scope for this triage pass per campaign guide (no Rust seed
source changes).

## Secondary finding in the same spec (different root cause, noted here to
avoid a second doc for the same file)

`sugar_plugin_spec.spl`'s "FR-PLUG-0004 blocker: Cranelift matrix ops still
use generic fallback" example also fails, but for an unrelated reason: it
content-checks `src/compiler/70.backend/backend/cranelift_codegen_adapter.spl`
for a function named `translate_binop` with a 6-arg signature and a comment
"# Pow, MatMul, Broadcast ops: fall back to integer add". Neither currently
exists — the function is now `cl_translate_binop` (8 args, added `cl_module`
and `right_operand`), and `MatMul`/`BroadcastAdd`/`BroadcastSub`/
`BroadcastMul`/`BroadcastDiv`/`BroadcastPow` each now dispatch to a real
`__simple_runtime_*` call (see lines 877-936); only `Pow` and genuinely
unmapped ops still hit the `case _:` generic-iadd fallback, with an updated
comment "# Pow and unsupported future ops still use the scalar fallback."

This is not a mechanical rename (STALE-TEST) — the assertion's entire premise
(matrix ops use the generic fallback) is now false because the feature
progressed, so any fix requires deciding what the new positive contract
should assert, which is a product/test-design call rather than a triage-scope
edit. Left unmodified per the "never weaken/rewrite an assertion to force
green" rule; flagging for whoever owns FR-PLUG-0004 to either retitle this
example to assert the new `MatMul`/`Broadcast*` dedicated-lowering contract,
or split it into "resolved" + "Pow still pending" sub-checks.

## Second affected cluster: `test/unit/app/branch_coverage_N_spec.spl` (whole-suite unit triage, 2026-07-20)

Confirmed the SAME `.?` identity-passthrough root reproduces the whole
`branch_coverage_N_spec.spl` block found in the `test/unit/` WALLED sweep.
All `branch_coverage_1_spec.spl` .. `branch_coverage_25_spec.spl` (and up to
at least N=25; 50 total files matched the sweep glob) are **byte-identical
duplicates** (`diff branch_coverage_1_spec.spl branch_coverage_10_spec.spl`
→ no output) of one file. Re-run individually on the deployed binary
(`bin/release/x86_64-unknown-linux-gnu/simple`, `--no-session-daemon`,
90s timeout) — NOT a timeout/false-positive; every one of the 4 sampled
(`_1`, `_10`, `_15`, `_25`) genuinely fails with the identical 3 examples out
of 75:

- `"dict get - exists"` (`test/unit/app/branch_coverage_1_spec.spl:408-410`):
  `check(d.get("key").?)` — `.?` on the `Option` returned by
  `Dict.get("key")` (present key) evaluates to the string `"value"` itself
  (not `true`); `check()` (`expect(condition: bool).to_equal(true)`) reports
  `expected value to equal true`.
- `"option is some"` (line 418-420): `check(opt.?)` on `Some(42)` evaluates to
  `42`, not `true` → `expected 42 to equal true`.
- `"option chain - some/some"` (line 430-432): `check(opt1.?)` on
  `Some(Some(10))` evaluates to `10`, not `true` → `expected 10 to equal
  true`.

Same mechanism as the `sugar_plugin_spec.spl` cases above — `.?` on a
present/non-nil value passes the value through unchanged instead of
converting to boolean `true`. All three assertions are the officially
prescribed `.?` idiom and are correct as written; left unmodified per the
"never weaken an assertion" rule.

**Affected specs (all share this one root, do not file separately):**
`test/unit/app/branch_coverage_1_spec.spl` through `branch_coverage_25_spec.spl`
(inclusive) plus `branch_coverage_10_spec.spl`..`branch_coverage_25_spec.spl`
duplicates already covered by the same numeric range — i.e. every
`test/unit/app/branch_coverage_N_spec.spl` file in the repo (50 files at time
of writing, all byte-identical). 3 failures each, 150 failures total, one
root cause.
