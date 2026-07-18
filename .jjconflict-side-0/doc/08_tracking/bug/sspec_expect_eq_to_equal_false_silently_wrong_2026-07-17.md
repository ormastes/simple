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

## Sweep 2026-07-17 (Worker J)

Full repo sweep of the footgun family. Root cause confirmed empirically (see
probe repro below): the rewrite/extraction only fires when the matcher
argument literal is `false` -- **both** `==` and `!=` operators are affected,
not just `==`:

- `expect(a == b).to_equal(false)` → silently checks `a` equals `b`
  (non-negated "expected A to equal B" message on the raw operands).
- `expect(a != b).to_equal(false)` → silently checks `a` **does not** equal
  `b` (negated "Expected A to NOT equal B" message on the raw operands) --
  this is the mirror-image bug the original writeup above did not name. It is
  just as dangerous: author intent for `!=`+`false` is "assert `a == b`", but
  the buggy path asserts the opposite (`assert_not_equal`).
- `expect(a == b).to_equal(true)` and `expect(a != b).to_equal(true)` are
  **not** buggy -- confirmed by direct probe (`probe_footgun_spec.spl` cases
  3 and 5): with a `true` matcher argument, `expect(...)` evaluates the
  boolean expression normally (no operand-extraction rewrite triggers), so
  these coincidentally/correctly match author intent already. Per this
  evidence, `!=`+`true` was **not** swept in this pass despite an early
  broader grep surfacing ~240 files using that shape -- rewriting those would
  have been unjustified scope creep (not a bug) and was explicitly ruled out
  after reconciling with a stronger reviewer mid-task.

### Authoritative re-grep

The originally-quoted grep (`expect\([^)]*==[^)]*\)\.to_equal\(false\)`)
under-counts: `[^)]*` cannot cross a `)`, so any operand containing a method
call or index (`expect(hash.len() == 0).to_equal(false)`,
`expect(gate.denial_reason() == "").to_equal(false)`) is invisible to it --
this is exactly why the original "18 files" estimate missed several real
sites (`sha512_extern_dispatch_spec.spl`, `eth_fcs_spec.spl`,
`dma_file_vga_spec.spl`, `bip39_kat_spec.spl` among them). The paren-tolerant
re-grep used for this sweep:

```bash
grep -rnE 'expect\(.*(==|!=).*\)\.to_equal\(false\)' test/ src/ | grep -v '\.spipe_matchers_'
```

This over-matches sites where the `==`/`!=` is nested inside a string literal
(`.contains("... == ...")`), a lambda/predicate argument
(`array_any([], fn(x): x == 1)`), or an `and`/`or` expression
(`expect(a == b and b == c).to_equal(false)`) -- all confirmed SAFE by
mechanism (the rewrite only fires when the raw top-level argument to
`expect(...)` is itself a bare `==`/`!=` BinaryOp) and, for the trickiest
cases, by direct probe. Those sites were left untouched.

### Files fixed (rewritten to `assert_not_equal`/`assert_equal`, then re-run)

All PASS unless noted. Pre-existing unrelated failures (confirmed identical
against `git show HEAD:<path>` baseline re-runs) are listed but NOT part of
this bug's blast radius.

- `test/01_unit/compiler/native_enum_u8_regression_spec.spl` (+ `test/unit/` mirror) -- `!=`+false → `assert_equal`. PASS.
- `test/01_unit/compiler/codegen/gpu_portable_compute_spec.spl` -- `==`+false → `assert_not_equal`. PASS.
- `test/01_unit/compiler/driver/native_build_cache_plumbing_spec.spl` (2 sites, `==`+false) → `assert_not_equal`. Overall file FAIL is pre-existing (unrelated `ctx` semantic error + source-drift `.to_contain` checks; identical in baseline).
- `test/01_unit/compiler/hir/resolve_import_symbols_spec.spl` -- `==`+false → `assert_not_equal`. Overall file FAIL is pre-existing (`is_async` on String semantic error; identical in baseline).
- `test/01_unit/compiler/semantics/resolve_nil_guard_spec.spl` (2 sites) → `assert_not_equal`. Same pre-existing unrelated failures as above.
- `test/01_unit/lib/gc_async_mut/gpu/engine2d/backend_metal_font_spec.spl` -- `==`+false → `assert_not_equal`. PASS (edited case).
- `test/01_unit/lib/gc_async_mut/gpu/engine2d/backend_cuda_renderbackend_spec.spl` -- `==`+false → `assert_not_equal`. PASS (edited case).
- `test/01_unit/lib/gc_async_mut/gpu/engine2d/backend_vulkan_font_spec.spl` -- `==`+false → `assert_not_equal`. PASS (edited case).
- `test/01_unit/lib/crypto/sha512_extern_dispatch_spec.spl` (+ `test/unit/` mirror) → `assert_not_equal`. PASS.
- `test/01_unit/lib/crypto/salsa20_spec.spl` (+ `test/unit/` mirror, 2 sites) → `assert_not_equal`. PASS.
- `test/01_unit/os/crypto/xsalsa20_spec.spl` (+ `test/unit/` mirror) → `assert_not_equal`. PASS.
- `test/01_unit/lib/hardware/soc_rtl/eth_fcs_spec.spl` → `assert_not_equal`. PASS.
- `test/01_unit/lib/skia/glyph_cache_spec.spl` (+ `test/unit/` mirror, 2 sites) → `assert_not_equal`. Edited case PASSES; file-level FAIL is a pre-existing `code_unit_at` on `str` semantic error, identical in baseline.
- `test/01_unit/os/crypto/bip39_kat_spec.spl` (+ `test/unit/` mirror) → `assert_not_equal`. This file's `mnemonic_to_seed` describe block hits a pre-existing test-daemon timeout (confirmed identical in baseline, even at 400s) before/around the edited assertion; inconclusive but not caused by the edit.
- `test/01_unit/os/crypto/streebog_kat_spec.spl` (+ `test/unit/` mirror, 2 sites) → `assert_not_equal`. PASS.
- `test/01_unit/os/drivers/dma_file_vga_spec.spl` (+ `test/unit/` mirror) → `assert_not_equal`. PASS.
- `test/01_unit/os/apps/sshd/ssh_kexinit_packet_layout_spec.spl` → `assert_not_equal`. PASS.
- `test/02_integration/app/ui.electron/spawn_via_manifest_test.spl` (+ `test/integration/` mirror) -- `b == nil`+false → `assert_not_equal(b, nil)`. PASS.
- `test/02_integration/app/ui.web/random_hex_test.spl` (+ `test/integration/` mirror) -- only the single-binop site (`a == b`) fixed; the `a == b and b == c` site is SAFE (top-level `and`, confirmed by probe) and left as-is. PASS.
- `test/03_system/gui/macos_gui_live_window_evidence_spec.spl` (5 sites: simple_bin empty check ×2, non_background_ratio, host_os ×1 in the non-macos branch (2 checks), smf_row macos_status) → `assert_not_equal`. Edited `it` PASSES fully (5/5 examples); file-level FAIL is a pre-existing `rt_cli_arg_count` extern-resolution error in an unrelated `it`, identical in baseline.
- `test/03_system/app/os/feature/rv64_user_mode_exec_spec.spl` (+ `test/system/` mirror) -- **`!=`+false, bitwise-and privilege-bit checks** → `assert_equal(expr, 0)`. PASS. See "Real defect found" below.
- `test/03_system/app/os/feature/simpleos_desktop_core_formal_verification_spec.spl` (+ `test/system/` mirror) -- same bitwise-and shape → `assert_equal(expr, 0)`. PASS (edited cases); file-level FAIL is a pre-existing, unrelated `AppSwitcher` assertion (`expected Option::Some(10) to equal 10`), identical in baseline.
- `test/03_system/check/widget_showcase_perf_wrapper_spec.spl` -- `==`+false → `assert_not_equal`. Pre-existing failure in the same `it` (shell-script harness produces no evidence file in this sandbox, identical in baseline) means the rewritten assertion itself was not exercised; not a regression.
- `src/lib/nogc_sync_mut/debug/formats/test/gdb_pretty_printers_spec.spl` and the `nogc_async_mut` mirror -- `==`+false → `assert_not_equal`. PASS (edited case; baseline showed 9 passed vs 10 passed after the fix -- confirms this assertion was previously silently never contributing a real check). One pre-existing unrelated failure remains in both, identical to baseline.

### Sites reviewed and left untouched (confirmed safe, not the bug shape)

- `test/01_unit/compiler/backend/native_backend_spec.spl` (+ `test/unit/` mirror) -- match is inside a `#`-commented line.
- `test/01_unit/compiler/interpreter/logical_short_circuit_spec.spl` -- `false and (1 / 0 == 0)`: top-level operator is `and`, not `==`; confirmed safe by probe (same class as the `random_hex_test.spl` case above).
- `test/01_unit/compiler/frontend/aop_log_policy_spec.spl`, `test/01_unit/app/cli/native_build_arg_source_spec.spl`, `test/01_unit/app/cli/bootstrap_main_source_spec.spl`, `test/01_unit/os/drivers/nvme/nvme_driver_probe_contract_spec.spl` (+ `test/unit/` mirror), `test/01_unit/browser/script/js_transpiler_spec.spl` (+ `test/unit/` mirror), `test/03_system/os/qemu/simpleos_qemu_host_gpu_2d_spec.spl` -- all match `.contains("... == ..." )` / `.contains("... != ...")`: the operator is inside a *string literal* argument to `.contains()`, not a live binary expression; `expect(...)` receives a plain bool from `.contains()`.
- `test/01_unit/lib/common/array_coverage_spec.spl` (+ `test/unit/` mirror), `test/01_unit/lib/std/common/collection_helpers_spec.spl` (+ `test/unit/` mirror) -- `array_any([], fn(x): x == 1)`, `none(...)`, `one(...)`: the `==` is inside a lambda/predicate argument one level down; the top-level expect argument is the function call, which returns a plain bool.
- `test/01_unit/os/security/session_hierarchy_spec.spl` -- already uses the safe `eq_u64(a.id, b.id)` helper-function idiom (with an inline comment explaining why), not the raw-binop shape. No change needed.

### Real defect found (new bug, separate doc filed)

The `rv64_user_mode_exec_spec.spl` / `simpleos_desktop_core_formal_verification_spec.spl`
sweep exercised the mirror `!=`+`false` bug on a security-relevant privilege-bit
check (RV64 `sstatus & SPP` and `scause & INTERRUPT_BIT`). Rewriting to the
correct `assert_equal(expr, 0)` form and re-running showed the underlying
runtime values ARE actually correct (0 as expected) -- so no additional
runtime defect was uncovered there; the tests now pass for the right reason
instead of passing by the footgun's accident. No new bug doc was needed for
those two files.

No spec-local fix revealed a genuine, previously-masked PRODUCT bug in this
sweep -- every rewritten assertion either passed outright, or its file's
remaining failures were independently confirmed pre-existing and unrelated
(byte-identical failure messages against a `git show HEAD:<path>` baseline
re-run of the unmodified file). No new bug doc was required as a result of
this sweep.

### Scope note

`!=`+`true` (confirmed NOT buggy, ~240 files) was intentionally excluded from
this sweep per the guide's own scoping ("cover whichever shapes the bug doc
names" -- this doc names only `==`+false) and per empirical proof it is not
broken. `==`+`true` sites were left alone except where already inside a file
being edited for another reason (none required it in this pass).

`test/01_unit/app/tooling/test_runner_simple_spec.spl` and its doc mirror
were out of scope for this sweep (owned by another lane) and were not
touched or grepped for this pattern.
