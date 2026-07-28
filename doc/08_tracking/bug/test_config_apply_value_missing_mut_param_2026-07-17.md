# test_config.spl: apply_test_config_value mutates its own stack frame only, never the caller's TestConfig

**Date:** 2026-07-17
**Severity:** medium (the `test:` section of `config/simple.test.sdn` never actually
changes runtime behavior for the keys routed through this helper, though the
one current call site, `load_test_config_from_path`, has ALSO been hard-bypassed
with an early `return config` before it ever calls the parser — see Notes — so
this is not currently reachable in production)
**Status:** open — language/runtime defect, not fixed here (found while writing
new hardening unit specs for `src/lib/nogc_sync_mut/test_runner/test_config.spl`,
out of scope for that task)

## Symptom

`apply_test_config_value(config: TestConfig, key: text, value: text)` (in
`src/lib/nogc_sync_mut/test_runner/test_config.spl`) assigns fields onto its
`config` parameter (e.g. `config.run_sdoctests = value == "true"`) but declares
that parameter without `mut`. Any assignment inside the function only mutates
the callee's own local copy — the caller's `TestConfig` is completely
unaffected, even though the function has no return value and every call site
assumes in-place mutation.

This silently breaks `parse_test_config_content`, which calls
`apply_test_config_value(config, key, value)` (both for top-level keys and for
`cpu_throttle.*` keys via `_apply_session_max`'s sibling branches) and then
returns the SAME `config` at the end of the function, assuming the helper
mutated it. It did not.

## Minimal repro

```simple
use std.test_runner.test_config.{TestConfig, apply_test_config_value, parse_test_config_content}

val config = TestConfig.defaults()
apply_test_config_value(config, "run_sdoctests", "true")
print(config.run_sdoctests)  # false -- should be true

val config2 = TestConfig.defaults()
val parsed = parse_test_config_content(config2, "test:\n  run_sdoctests: true\n")
print(parsed.run_sdoctests)  # false -- should be true
```

Confirmed on `src/compiler_rust/target/release/simple` (bootstrap seed) both
via direct interpretation and via a minimal isolated repro with a throwaway
struct (`struct Probe: flag: bool` / `fn set_it(p: Probe): p.flag = true`),
which surfaces the underlying diagnostic before falling back to the
interpreter:

```
[INFO] JIT compilation failed, falling back to interpreter: HIR lowering error:
Memory safety error [W1006]: mutation without mut capability (field_0):
mutation requires `mut` capability on the receiver while lowering set_it at 5:12
after set_it: false
```

By contrast, direct field assignment WITHIN `parse_test_config_content`'s own
body (the `CI` env var override block at the end of the function,
`config.ci_mode = true` etc., not routed through a helper function call) DOES
correctly propagate to the returned struct — confirming the defect is
specifically about mutating a struct THROUGH a separate function call whose
parameter lacks `mut`, not about struct mutability in general.

## Root cause

`fn apply_test_config_value(config: TestConfig, key: text, value: text):`
needs `fn apply_test_config_value(mut config: TestConfig, key: text, value: text):`
for the field writes inside it to be visible to the caller. Every call site
(`parse_test_config_content`'s two call sites) would then also need `config`
to be a `mut`-eligible binding, and `_apply_session_max` has the identical
shape and would need the same fix.

## Impact

Currently NOT observable in production: `load_test_config_from_path` (the only
caller of `parse_test_config_content` reachable from `TestConfig.load()`) has
an early `return config` before it ever reads `config_path` or calls
`parse_test_config_content`, with a comment noting "the SDN config parser
still hits interpreter iteration bugs on some paths; daemon defaults are the
resource boundary until that parser is fixed." This bug is a plausible
contributor to whatever motivated that bypass. If/when the bypass is lifted,
this defect would silently make every boolean/threshold key in
`config/simple.test.sdn`'s `test:` section a no-op.

## Suggested fix direction (not implemented here)

Add `mut` to the `config` parameter of `apply_test_config_value` and
`_apply_session_max`, then re-verify `parse_test_config_content` end-to-end
(a real regression test, not just checking the function compiles) before
lifting the `load_test_config_from_path` bypass.

## Cross-refs

Found while writing `test/01_unit/lib/test_runner/test_config_spec.spl`
(new hardening unit spec, task: pure-Simple test-runner engine package
hardening). That spec pins the current (broken) contract explicitly rather
than asserting the intended-but-unreachable behavior.
