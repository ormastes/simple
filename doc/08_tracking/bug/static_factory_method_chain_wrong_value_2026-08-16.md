# Chaining a method off a static factory call fails to resolve the method
## Open 2026-09-16 — needs owner triage

Reviewed in the 2026-09-16 bug-ledger normalization pass; no resolution
evidence found in the body. This is bookkeeping, not verification.

**Date:** 2026-08-16
**Status:** FIXED 2026-11-13 (lane p3-misc-b) — non-repro at release/1.0.0 tip
**Component:** compiler — type inference / method resolution in nested call context

## Symptom

Calling a method directly on the result of a `static fn` factory, when that
whole expression is nested inside another call (such as `expect(...)`), fails
with:

```
semantic: method 'double' not found on value of type object in nested call context
```

The receiver's type is erased to `object`, so method lookup finds nothing.
Binding the same factory result to a `val` first resolves correctly.

## Minimal reproduction

```simple
class Box:
    n: int
    me double() -> int:
        return self.n * 2
    static fn create(n: int) -> Box:
        return Box(n: n)

describe "chain probe":
    it "bound to a val first":          # PASSES
        val b = Box.create(21)
        expect(b.double()).to_equal(42)

    it "chained off the static factory":  # FAILS
        expect(Box.create(21).double()).to_equal(42)
```

Result: `declared>=2 executed=2 passed=1 failed=1`. The two examples are
semantically identical; only the binding differs.

## Impact

Silently forces a workaround: every call site must introduce a `val` binding
even where a chained expression is the natural, shorter form. Found while
converting the smux legacy specs to Modern SSpec
(`smux_legacy_specs_zero_examples_red_2026-08-16.md`) — 9 of 20 examples in
`test/01_unit/os/smux_spec.spl` and 6 of 21 in
`test/01_unit/os/smux/smux_dashboard_spec.spl` failed for this reason alone.
Those specs now bind a `val` in every example and carry a comment pointing
here, per the repo rule against silently normalizing a workaround.

## Notes on evidence

Observed with `bin/release/x86_64-unknown-linux-gnu/simple`, which
self-identifies as the Rust bootstrap seed. It could not be cross-checked
against a pure-Simple self-hosted binary: `bootstrap/stage1|2|3/simple` have no
`test` command, `release/x86_64-unknown-linux-gnu/simple` core-dumps on
`test --help`, and `build bootstrap` terminates inside Stage 1 without a
verdict. Independently corroborated upstream by
`deployed_selfhost_test_subcommand_segv_blocks_bootstrap_2026-08-16.md`.
Whether the defect is seed-only or also present in a self-hosted
compiler is therefore **unverified**.

## Unblock condition

Preserve the declared return type of a `static fn` through nested call
contexts so method resolution sees `Box`, not `object`. Re-run the
reproduction above; both examples must pass.



---

## Verification addendum 2026-11-13 (lane p3-misc-b)

Re-ran the record's minimal reproduction verbatim (class Box + static
`create`, `expect(Box.create(21).double()).to_equal(42)`) on the
release/1.0.0-tip seed: BOTH examples pass, spec verdict 2/2 GREEN. The
receiver type is no longer erased to `object` in nested call context —
presumably fixed with the nested-call/method-resolution work now at HEAD.
Closing as verified non-repro.