# Atom.swap with a placeholder lambda rebinds the receiver to the lambda result

- Status: OPEN (2026-09-12)
- Area: lib / nogc_async_immut atom + placeholder-lambda desugaring
- Found by: lane L2 (runtime hot paths) while establishing a before/after
  baseline for an unrelated `PersistentSet.intersection` change. Out of L2's
  scope, not fixed here.

## Symptom

`var atm = Atom.new(PersistentMap.empty())` followed by
`atm.swap(_1.set("name", "Alice"))` leaves `atm` bound to the *result of the
inner expression* rather than to the Atom. The next `atm.deref()` therefore
dispatches on a `str` (or an `i64`), not on an Atom:

```
semantic: method `deref` not found on type `str` (receiver value: Alice)
semantic: method `deref` not found on type `i64` (receiver value: 2)
```

`_1.set("name", "Alice")` should build a closure `\m: m.set("name", "Alice")`
that `swap` applies to the current value; the value observed in the receiver
("Alice", `2`) is the *argument* of `set`, so the placeholder lambda is being
collapsed rather than passed.

## Repro

```
bin/simple test test/01_unit/lib/immut/integration_spec.spl
```

Failing examples (both in `describe "Atom holding persistent map"`):

- `it "swap adds entries to the map"` — `test/01_unit/lib/immut/integration_spec.spl:95`
- `it "multiple swaps accumulate entries"` — `test/01_unit/lib/immut/integration_spec.spl:101`

The mirrored `test/01_unit/lib/common/immut/integration_spec.spl` fails the
same two examples identically.

## Evidence

Measured 2026-09-12 in worktree `/home/yoon/dev/simple-l2` at base
`79a67e79135`, binary `bin/release/aarch64-unknown-linux-gnu/simple`,
sha256 `3d120a6f9ab5704b...`:

```
SPEC FILE VERDICT: test/01_unit/lib/immut/integration_spec.spl outcome=ERROR declared>=20 executed=20 passed=18 failed=2 skipped=0 dropped=0
SPEC FILE VERDICT: test/01_unit/lib/common/immut/integration_spec.spl outcome=ERROR declared>=20 executed=20 passed=18 failed=2 skipped=0 dropped=0
```

Both verdicts are byte-identical with and without L2's `PersistentSet`
change in the tree, so the failure is pre-existing and unrelated to
`PersistentSet`. The first example in the same `describe`
(`"atom wraps a persistent map"`, which calls `deref()` without a prior
`swap`) passes, which isolates the defect to the `swap` + placeholder-lambda
path rather than to `Atom` construction or `deref` itself.

## Not done here

No fix and no skip. These two examples must stay failing and visible until the
placeholder-lambda/`swap` path is repaired; do not tag them
`@tag:in-development` to quiet the suite.
