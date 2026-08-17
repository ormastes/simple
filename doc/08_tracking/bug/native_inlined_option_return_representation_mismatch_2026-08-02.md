# Native inlined Option return representation mismatch

Status: open  
Severity: P1 native semantic parity  
Fix owner: `/root/native-option-return-representation` — TRACKED, NOT PARALLEL-CLAIMABLE

## Reproduction

A no-stub pure-Simple Stage 3 build of the async database probe links and runs,
but this comparison returns false for a row that contains the requested ID:

```simple
row.get("run_id") == Some(run_id)
```

Disassembly shows the inlined `SdnRow.get` result as a bare text handle while
`Some(run_id)` is constructed with `rt_enum_new`. `rt_native_eq` therefore
compares two different physical representations.

The same probe also showed that printing the raw result of `text.starts_with`
passes an unboxed runtime `i64` boolean to `rt_println_value`, which renders as
`nil`; branching on the predicate remains the correct discriminator. That bool
boxing defect is already covered by the native MC/DC work and is not duplicated
here.

## Bounded mitigation result

An explicit nil check plus unwrap was tested and rejected: the pure-Simple
native probe still returned false. The consumer workaround was removed rather
than committing an ineffective divergence; the seed/interpreter behavior stays
covered by the existing database regression.

## Compiler repair required

Native lowering must keep function-returned and inlined `Option<T>` values in
one canonical representation across calls, inlining, equality, pattern
matching, `??`, `?`, and `unwrap`. Add positive/negative focused probes for
text and one non-text payload before changing the representation.

## 2026-08-08 re-verification (rank-2 finding from
`doc/09_report/infra/aot_lane_regression_fence_audit_2026-08-07.md`)

**Free-function shape: NOT reproducible today — appears fixed for this
shape.** A minimal fixture keeping the same `Option<text>`-equality shape as
the original repro (`row.get("run_id") == Some(run_id)`), but using a
top-level function instead of a struct method, produces the CORRECT result
under `native-build`:

```
fn lookup(id: text) -> Option<text>:
    if id == "": return None
    return Some(id)
```
`lookup("run_id") == Some("run_id")` → `match` (correct), a mismatched
`Some("other_id")` → `no-match` (correct), and `lookup("") == None` →
`match` (correct). Verified against the interpreter reference
(`SIMPLE_EXECUTION_MODE=interpret bin/simple run`), which agrees. Fixture:
`test/fixtures/native_option_eq_representation/main.spl`. Fence:
`scripts/check/check-native-option-eq-representation.shs` (sabotage-verified
2026-08-08: mutating the expected literal flips the gate to `FAIL` with a
literal diff, restoring it flips back to `PASS`).

**2026-08-08 re-re-verification: the blocking crash is FIXED; struct-method
`==` shape is now VERIFIED CORRECT; a separate, narrower native-only
divergence remains OPEN on the pattern-bind/unwrap surface.**

The `undefined field 'kind'` crash described in the previous note was fixed
same-day by `100a9aadcc4` ("fix(mir): stop wrapping an already-optional
receiver type in Some()"): `method_calls_literals.spl:940` was wrapping the
already-Option-desugared `receiver.type_` in an extra `Some(...)`, turning an
absent type into `Some(nil)` instead of `None`; the callee
`mir_hir_type_is_shared_resource` (`mir_lowering_stmts.spl:103-127`) matched
`case Some(ht)` with `ht == nil` and dereferenced `ht.kind`. (The earlier
note's pointer to `switch_operators_calls.spl:1596-1618` was a *sibling*,
narrower guard for a different `?`-operator/mutable-var shape — not the
actual fix site; correcting that here so the pointer isn't propagated
further.)

With the crash gone, the struct-method `==` shape was re-verified today with
a fresh minimal fixture
(`test/fixtures/native_option_eq_representation/struct_method_main.spl`,
same hit/miss/none shape as the free-function fixture but using
`Lookup(id: ...).get() -> Option<text>` as an instance method):
`native-build` succeeds (rc=0, zero occurrences of `undefined field 'kind'`
in the build log) and the binary prints
`hit=match miss=no-match none=match` — all three cases correct, matching the
interpreter reference. **This shape is now gated** by
`scripts/check/check-native-option-eq-representation.shs` (extended today
with a second build+run for the struct-method fixture, run separately from
the free-function build so a regression in either shape is attributed
correctly; sabotage verification recorded further down this doc once run).

A **different, still-open** native-only divergence was found on the
pattern-bind/unwrap surface for the same struct method — this is squarely
inside this bug's own repair criterion above ("pattern matching … `?` …
unwrap"), so it is recorded here rather than closing the doc:
```simple
class Box:
    v: i64

impl Box:
    fn label() -> Option<text>:
        if self.v > 0:
            return Some("positive")
        None

fn main() -> i64:
    val b = Box(v: 42)
    val r = b.label()
    if val lbl = r:
        if lbl != "positive":
            return 1
    else:
        return 2
    print("option-struct-method-ok")
    0
```
Under `SIMPLE_EXECUTION_MODE=interpret bin/simple run`, this prints
`option-struct-method-ok` and exits 0 (correct — `lbl` binds to `"positive"`,
`lbl != "positive"` is false). Under `native-build` (default LLVM backend,
`--entry-closure`), the build succeeds (rc=0, no crash) but the binary exits
1 with no stdout — meaning `if val lbl = r:` bound (else branch, `return 2`,
was not taken) but `lbl != "positive"` incorrectly evaluated true. This is
consistent with the same class of representation mismatch this doc tracks,
now visible on the `if val` unwrap path specifically rather than blocked by
the crash. Not yet root-caused or fenced; not gated by the check script
(gating only the verified-correct `==` shape per this doc's own rule that a
red case must not be folded into a script required to exit 0).

**A separate, unrelated finding surfaced while investigating the same
lane's claim that the pre-existing `native_immutable_fn_receiver.spl`
fixture reproduces the `'kind'` crash: it does not.** The script
`scripts/check/check-native-immutable-fn-receiver.shs` requires a
self-hosted `SIMPLE_BIN` (it explicitly rejects the Rust seed) plus
`--backend cranelift`; the only self-hosted binary available today
(`bootstrap/stage3/x86_64-unknown-linux-gnu/simple`) segfaults (rc=139)
compiling this repo's full `--source test/fixtures` tree, a pre-existing,
separately known issue not further investigated here — so the script's exact
combination could not be run end-to-end. Using the script's *source-root and
entry arguments* (`--source test/fixtures/compiler --entry-closure`,
`SIMPLE_LIB` set) but the Rust seed binary and its default (LLVM) backend
instead, the build produces **zero** occurrences of `undefined field 'kind'`
in the log; it exits 1 with a *different* error, `MIR lowering error:
unresolved method call: read` (cross-module `impl`-block method resolution).
`unresolved method call` is raised during MIR lowering, before backend
selection, so it is not expected to be backend-specific — but this was not
independently confirmed on a self-hosted binary. Net: the other lane's
specific claim — that this fixture reproduces the `'kind'` crash — is not
supported by any run performed today; a nonzero exit was evidently read as
confirmation without checking the error text, the same mistake this
re-verification pass was launched to correct. The `unresolved method call:
read` failure is real (reproduced on the seed) and worth its own look, but
it is not this bug and not the `'kind'` crash either.

**False-green spec.** No spec asserts the exact `== Some(...)` shape named
in this doc. The closest real candidate exercising `SdnRow.get()`'s
`Option<text>` return under a database-realistic query is
`test/01_unit/lib/database/database_query_spec.spl:31-32,51-52,84-87,104-105`
(`expect(results[0].get("status")?).to_equal("Open")`, using `?`-unwrap
rather than `==`). Like every `*_spec.spl` in the tree, it only ever runs
under `bin/simple test`'s hard-defaulted tree-walk interpreter (see the
audit doc), so it cannot observe the AOT lane either way — it is a
false-green risk in the same structural sense the audit describes, not a
verified false-green of this exact defect. (Attempting to actually run it
to observe pass/fail timed out in this session and was not completed —
UNVERIFIED.)


## 2026-08-17 CORE-P1 triage: DID NOT REPRODUCE / fix present in current source

Verified against CURRENT SOURCE (content, not SHA ancestry) during the crit_01
CORE-P1 sweep. Fix present and gated. `src/compiler/50.mir/_MirLoweringExpr/expr_dispatch.spl:1543` normalizes inlined returns under `case HirTypeKind.Optional(_)` via `result = self.ensure_option_handle(result, found_return)`, and the Eq path (:2286-2306) boxes the unwrapped side through the same `ensure_option_handle` before `rt_native_eq`. The gate this doc names exists and is real: `scripts/check/check-native-option-eq-representation.shs` native-builds two fixtures with `--entry-closure` and asserts stdout equals `hit=match miss=no-match none=match` for both.
