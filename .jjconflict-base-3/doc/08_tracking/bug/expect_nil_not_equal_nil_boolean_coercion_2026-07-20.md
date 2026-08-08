# `expect(nil != nil)` yields nil instead of boolean false (only when both sides are nil)

**Status:** resolved — NOT REPRODUCIBLE at HEAD (verified 2026-08-01)
**Found:** 2026-07-20 (whole-suite triage campaign, test/01_unit shard)
**Area:** interpreter — `!=` operator / SSpec `expect()` boolean coercion

## Resolution (2026-08-01)

Does not reproduce under the seed
(`src/compiler_rust/target/bootstrap/simple`). `nil != nil` evaluates to a
proper boolean `false`; the exact construct from the Symptom section now
passes:

- `test/01_unit/lib/ffi/ffi_signature_spec.spl` — **7/7 green** (the file has
  since been migrated off `.?` to the `== nil` form, so the residual failure
  described in the note below is also gone).
- The reported repro rewritten to the precise `!= nil` shape
  (`expect(m.get("T32_NonExistent") != nil).to_equal(false)`) passes, as does
  its non-nil sibling.

**The green is not vacuous.** The matcher was proven strict against nil before
trusting the pass: `expect(Option::None).to_equal(false)`, `.to_equal(true)`,
`.to_equal(0)`, and `expect(false).to_equal(0)` all still FAIL. So if
`x != nil` were still yielding raw `nil`, the `.to_equal(false)` assertion
would fail rather than pass by coercion.

**Likely fixed by** `10a7c5f922a` *"fix(spec): assert_nil rejected typed
Option::None — and assert_not_nil silently PASSED it"*. The real root cause
was nil's two runtime representations (bare `Value::Nil` vs the `Option::None`
that a `T?` function returns for `return nil`), not a missing bool coercion in
`!=`. The root-cause hypothesis below is therefore superseded.

The report's confusing `expected nil to not equal nil` message is reproducible
today only from the *negated* matcher path (`expect(none).to_not_equal(none)`),
where it is a **correct** failure — consistent with the reporter's own hunch
that the message came from a negated matcher rather than a plain equality check.

**Regression guard:** `test/01_unit/lib/spec/nil_matcher_option_none_spec.spl`
gained a `nil-vs-nil comparison yields a strict boolean, not nil` block plus a
`the matcher never coerces nil to a boolean` block (8 examples; file 14 -> 22
passing). Each new assertion was mutation-checked — flipping its oracle makes
it fail — so the block cannot go silently vacuous.

## Note: recommended fix is NOT applied to the file (leaves 1 residual failure)

`test/01_unit/lib/ffi/ffi_signature_spec.spl` currently fails 2 of 7
examples via the known, already-filed `.?` identity-passthrough bug
pattern: `expect(sig.?).to_equal(true/false)`. The obvious migration is
`expect(sig.?)` -> `expect(sig != nil)` (value-preserving, per this
campaign's documented pattern). Trying that locally: the "retrieves by
name" case (`sig` non-nil, expects `true`) goes green, but the "returns nil
for unknown name" case (`sig` IS nil, expects `false`) trades its original
failure for a **different, genuine** failure (below) rather than passing —
so the spec still can't reach green either way. Per this campaign's rule
(leave GENUINE-BUG specs unmodified, file a doc instead of carrying a
partial edit), **the `.?` -> `!= nil` migration was NOT kept in the
file** — do that migration first when someone follows up on the failure
documented here.

## Symptom

With the `.?` -> `!= nil` migration applied locally for `sig`:

```
it "returns nil for unknown name":
    var m = FfiManifest.create()
    m.add("T32_Ping", 0, "i32")
    val sig = m.get("T32_NonExistent")   # FfiManifest.get() -> FfiSignature? ; returns literal nil here
    expect(sig != nil).to_equal(false)
```

Fails with:

```
✗ returns nil for unknown name
    expected nil to not equal nil
```

(Against the current, unedited file this same underlying case instead
shows the original `.?`-passthrough symptom: `expect(sig.?).to_equal(false)`
-> `expected nil to equal false`. Both are the same root defect area — nil
handling in comparisons/coercions — but the `!= nil` form surfaces the more
precise "nil doesn't coerce to boolean false" defect described below.)

`sig` is genuinely `nil` here (`FfiManifest.get(name: text) -> FfiSignature?`
in `src/lib/nogc_sync_mut/sffi/sffi_signature.spl:31-34` falls through to
`nil` when the entry isn't found). So `sig != nil` is `nil != nil`, which
should evaluate to boolean `false`. Instead it appears to evaluate to `nil`
(untyped/unboxed), which then fails `.to_equal(false)` with the confusing
message "expected nil to not equal nil" (the message itself looks like it
comes from a different/negated matcher path than a plain boolean equality
check, suggesting the `!=` comparison result isn't a clean `bool` by the
time it reaches `.to_equal()`).

The sibling case one line above it (`sig` genuinely non-nil,
`expect(sig != nil).to_equal(true)`) passes fine — the defect is specific
to the `nil != nil` (both-sides-nil) case.

## Root-cause hypothesis

Consistent with this codebase's known nil/Option-handling interpreter
quirks (see project reference notes on `.?` returning non-boolean and
general nil-comparison landmines): the `!=` operator's result, when both
operands are `nil`, does not get coerced to a proper `bool` (`false`) the
way a nil-vs-non-nil comparison does — it appears to propagate `nil`
itself as the comparison's "falsy" result instead of `false`, and that
raw `nil` then fails an explicit `.to_equal(false)` check (nil != false
by strict equality) rather than being treated as boolean false.

## Minimal repro

```
SIMPLE_RUST_SEED_WARNING=0 timeout 90 \
  /home/ormastes/dev/pub/simple/bin/release/x86_64-unknown-linux-gnu/simple \
  test test/01_unit/lib/ffi/ffi_signature_spec.spl --no-session-daemon
```

## Affected specs seen this shard

- `test/01_unit/lib/ffi/ffi_signature_spec.spl` — 2 examples currently fail
  via the known `.?` bug (not fixed in-file, see note above); "returns nil
  for unknown name" specifically will still fail with this doc's distinct
  `nil != nil` defect even after the `.?` -> `!= nil` migration is applied.
