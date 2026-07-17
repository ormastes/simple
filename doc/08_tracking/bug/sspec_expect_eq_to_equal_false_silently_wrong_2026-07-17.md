# SSpec: `expect(a == b).to_equal(false)` silently checks `a` equals `b` instead of asserting they differ

**Date:** 2026-07-17
**Severity:** high (silently asserts the OPPOSITE of what the test author
intended; a naive grep found 18 spec files using this exact pattern, listed
below -- not audited/fixed here, out of scope for this task)
**Status:** open — found incidentally while writing new hardening unit specs
for the test-runner engine packages; not fixed here (test-authoring landmine,
not something a spec-only task should patch in the runner/matcher source)

## Symptom

`expect(<a> == <b>).to_equal(false)` does NOT assert that the boolean
`(a == b)` equals `false` (i.e. that `a` and `b` differ). Instead the SSpec
`expect(...)` macro appears to special-case a bare `==` binary expression as
its argument and rewrite the whole chain to `expect(a).to_equal(b)`, ignoring
the trailing `.to_equal(false)` matcher entirely. This means any test written
as "assert these two values are NOT equal" via this pattern is silently
checking that they ARE equal instead.

`expect(<a> == <b>).to_equal(true)` happens to still produce the intuitively
correct result under the same rewrite (asserting `a` equals `b`), so the bug
is invisible for that spelling and only manifests for the `false` form.

## Minimal repro

```simple
describe "eq probe":
    it "checks two different strings are not equal":
        val a = "hello_aaa"
        val b = "hello_bbb"
        expect(a == b).to_equal(false)   # author intent: assert a != b

    it "checks two equal strings are equal":
        val a = "same"
        val b = "same"
        expect(a == b).to_equal(true)
```

Result on `src/compiler_rust/target/release/simple test`:

```
eq probe
  ✗ checks two different strings are not equal
    expected hello_aaa to equal hello_bbb
  ✓ checks two equal strings are equal
```

The first case reports a failure with message "expected hello_aaa to equal
hello_bbb" -- i.e. it actually ran `expect(a).to_equal(b)`, not
`expect(a == b).to_equal(false)`. A test author who *wanted* `a != b` to be
proven and got this failure would (correctly) conclude something is broken;
the more dangerous case is a test where `a` and `b` legitimately end up equal
by an unrelated bug -- that test would report a pass ("expected X to equal
X"), masking the fact that the author's real intent ("a != b") was never
checked.

## Correct alternative (already used elsewhere in the codebase)

Use the standalone assertion helpers instead of routing a boolean comparison
through `expect(...).to_equal(...)`:

```simple
assert_not_equal(a, b)   # correct, unambiguous
assert_equal(a, b)
```

This matches `.claude/rules/testing.md`'s existing guidance: "Standalone
assertions: `assert_true`, `assert_false`, `assert_equal`, `assert_not_equal`,
... -- use these for bare boolean/equality checks instead of
`expect(x).to_equal(true)`" -- though that guidance doesn't yet call out the
`false` case specifically, which is the more dangerous one.

## Impact / blast radius (not audited here)

A repo-wide grep for the exact shape
`expect(<expr> == <expr>).to_equal(false)` found 18 spec files using it,
e.g.:
- test/01_unit/compiler/codegen/gpu_portable_compute_spec.spl
- test/01_unit/compiler/driver/native_build_cache_plumbing_spec.spl
- test/01_unit/compiler/hir/resolve_import_symbols_spec.spl
- test/01_unit/compiler/semantics/resolve_nil_guard_spec.spl
- test/01_unit/lib/gc_async_mut/gpu/engine2d/backend_metal_font_spec.spl
- test/01_unit/lib/gc_async_mut/gpu/engine2d/backend_cuda_renderbackend_spec.spl
- test/01_unit/lib/crypto/sha512_extern_dispatch_spec.spl
- test/01_unit/lib/hardware/soc_rtl/eth_fcs_spec.spl
- test/01_unit/os/drivers/dma_file_vga_spec.spl
- test/01_unit/os/crypto/bip39_kat_spec.spl
- (8 more; re-run the grep below for the full list)

```bash
grep -rln 'expect([a-zA-Z_.()\[\]]* == [a-zA-Z_.()\[\]"]*)\.to_equal(false)' test/
```

Each of these should be reviewed and, where the intent was genuinely "assert
not equal", switched to `assert_not_equal(a, b)`. Not attempted here -- this
task only writes NEW specs for the test-runner engine packages and must not
edit existing specs or `src/**`.

## Suggested fix direction (not implemented here)

Either:
1. Make the `expect(...)` macro NOT special-case bare `==` expressions (treat
   the argument as a plain boolean and compare it against the matcher's
   argument like any other value), or
2. If the operand-extraction sugar is intentional (for nicer diff output),
   make it respect the trailing matcher's polarity (`to_equal(false)` should
   invert the comparison, or the macro should refuse to compile/should warn
   when a `==`/`!=` expression is combined with `to_equal(false)`/`to_equal(true)`
   respectively, since one of the two combinations is always redundant and the
   other always wrong today).

## Cross-refs

Found while writing `test/01_unit/lib/test_runner/result_wrapper_unit_spec.spl`
(new hardening unit spec for `std.test_runner.test_result_wrapper`); two of
its assertions originally used this pattern and were rewritten to
`assert_not_equal(...)` once the false pass/fail was traced to this DSL
behavior rather than a bug in the module under test.
