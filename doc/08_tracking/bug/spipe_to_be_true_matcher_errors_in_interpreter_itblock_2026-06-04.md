# Bug: `to_be_true()` / `to_be_false()` matchers error inside interpreter `it` blocks

Status: Open (worked around)

**Date:** 2026-06-04
**Area:** SPipe runtime, built-in matchers (`std.spec`)
**Status:** Open (worked around)
**Severity:** Medium

## Summary

`expect(x).to_be_true()` and `expect(x).to_be_false()` — both listed as
supported built-in matchers in `.claude/rules/testing.md` — cause the example to
FAIL when executed inside an `it` block under the interpreter, even when `x` is a
genuinely `true` bool. The equivalent `assert_true(x)` / `assert_false(x)`
standalone assertions pass on the same value, and `expect(x).to_equal(true)`
also behaves inconsistently.

Discovered while implementing the SFM (`.sfm`) feature: every SFM spec example
asserting via `to_be_true()` failed; converting to `assert_true(...)` (the form
`testing.md` already recommends for bare boolean checks) made them genuinely
green with no change to what is asserted.

## Reproduction

The failure also reproduces in unrelated existing code, e.g.
`test/02_integration/rendering/simd_parity_spec.spl`, so it is not SFM-specific.

Minimal shape:

```simple
use std.spec.*

describe "matcher":
    it "should accept a true bool":
        expect(true).to_be_true()      # FAILS in interpreter it-block
        assert_true(true)              # passes
```

Run via the interpreter:

```bash
bin/release/<triple>/simple test <spec>
```

Expected: 1 passed. Actual: the `to_be_true()` example is counted failed.

## Workaround

Use `assert_true` / `assert_false` (per `testing.md`: "use these for bare
boolean/equality checks instead of `expect(x).to_equal(true)`"). The SFM specs
(`test/03_system/feature/sfm/sfm_codec_spec.spl`,
`sfm_di_authz_spec.spl`, `sfm_samples_spec.spl`) adopt this form.

## Next step

Locate the `to_be_true`/`to_be_false` matcher handler in the interpreter's
`std.spec` dispatch and confirm whether the boolean value is being mis-tagged or
the matcher result is mis-reported, mirroring the related (fixed) tuple-map
matcher regression in
`spipe_interpreter_tuple_map_result_matcher_binding_2026-05-27.md`.
