# Seed SSpec runner keeps executing an example after `fail(...)`

Date: 2026-11-15
Status: open (found by lane seedparse; not fixed in that lane)

The seed SSpec runner does not stop an `it` block at `fail("...")`: statements after the
`fail(...)` call still execute (side effects and later assertions run), so one failing example
can emit extra output or secondary failures. Seen in
`test/01_unit/os/smf/dynsmf_lifecycle_close_spec.spl` (the `fail("owner-missing: ...")` /
`fail("fixture-construction-failure: ...")` guards at lines 53-73 are followed by code that
assumes the guard aborted).

Minimal repro (expected: one failure, `after` never printed):

```simple
describe "fail aborts example":
    it "stops at fail":
        fail("stop here")
        print "after-fail-reached"
        expect(1).to_equal(2)
```

Run: `<seed>/simple.exe test <spec>` from the worktree root with a relative path.
Observed (seed-attr2, 2026-11-15): `after-fail-reached` is printed, then `expected 1 to equal 2` also
fails: outcome=ERROR, 1 example, the one example reports both failures. `after-fail-reached` must not appear. `fail` should raise/abort the example like a failed `expect`.

Fix belongs in the seed SSpec runner (Rust) or the lib `fail` implementation; add a regression
spec that asserts the statement after `fail(...)` is not executed.
