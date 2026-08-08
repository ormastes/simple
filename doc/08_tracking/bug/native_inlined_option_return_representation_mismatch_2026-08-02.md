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

**Struct-method shape: UNVERIFIED, blocked by a separate crash.** The
original repro used a struct method (`SdnRow.get(...)`), not a free
function. Today, ANY struct/`impl`-block method — even a trivial
`fn always_run() -> i64: 99` with no `Option` and no field access at all —
crashes `native-build` with:
```
error: semantic: undefined field 'kind': cannot access field on value of type 'nil'
```
This reproduced on multiple from-scratch minimal fixtures (isolated
single-file, isolated two-file cross-module, inline-in-class-body, and
`impl`-block forms) AND on the pre-existing, previously-passing reference
fixture `test/fixtures/compiler/native_immutable_fn_receiver.spl` (driven
via `scripts/check/check-native-immutable-fn-receiver.shs`), using both the
default (LLVM) and `--backend cranelift` paths, with `bin/simple` (confirmed
by ELF/`--version` check to be the Rust seed at
`bin/release/x86_64-unknown-linux-gnu/simple`, not a stale artifact —
`src/compiler` mtimes are hours older than the binary, so this is not a
concurrent-edit artifact either) and with the pure-Simple stage3 binary
(`bootstrap/stage3/x86_64-unknown-linux-gnu/simple`, which instead segfaults
on this repo's full `--source test/fixtures` tree — a different, also
open, failure mode not further investigated here).

Because this crash blocks compilation before any method body executes, it is
NOT proof this specific representation-mismatch defect is fixed for the
struct-method shape that originally found it — it just means that shape
cannot be tested at all right now. This crash is a strictly more severe,
currently-unfenced blocker (it breaks essentially all struct-method
`native-build` compiles, not just Option-returning ones) and deserves its
own bug doc / triage; it was not filed separately here per scope, but is
recorded so it isn't lost. A matching guarded-but-narrower case already
exists in
`src/compiler/50.mir/_MirLoweringExpr/switch_operators_calls.spl:1596-1618`
(`receiver_declared_type`'s doc comment references the identical
`"undefined field 'kind': cannot access field on value of type 'nil'"`
message for a narrower `?`-operator/mutable-var shape) — the guard there
evidently does not cover the plain-method-call shape hit here.

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
