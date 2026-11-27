# `EnumName.Variant(named_args)` construction unresolved under `bin/simple test` (via transitively-called free fn)

- **Date:** 2026-07-20
- **Status:** open
- **Area:** SSpec `test` evaluator (Rust seed interpreter), same family as the
  documented test-path-vs-run-path divergence in
  `generic_class_static_method_unresolved_under_test_2026-07-20.md` /
  `enum_impl_static_fn_method_call_path_skips_impl_methods_2026-07-20.md`, but
  the failing symptom here is enum **variant construction** (`Enum.Variant(
  field: v, ...)`), not a static-method call, and it fires from inside a
  free function (`log_denial`) that a directly-called free function
  (`check_capability`) calls transitively — not a bare `EnumName.method()` in
  the spec body itself.

## Symptom

```
CapabilityPolicy
  ✗ default-deny policy denies InputInject
    semantic: unknown variant or method 'CapabilityDenied' on enum SecurityEvent
  ✓ granting InputInject allows it
```

`SecurityEvent` (defined `src/lib/nogc_sync_mut/security/types.spl:11`) DOES
declare a `CapabilityDenied(capability: text, window_id: text)` variant
(line 20) — confirmed present in source, so this is not a stale-test/renamed
symbol.

## Failing spec

`test/02_integration/app/ui.web/capability_gating_spec.spl`, `it "default-deny
policy denies InputInject"` (line 28) calls
`check_capability(policy, Capability.InputInject)` — a free function imported
from `common.ui.capability_policy`. `check_capability` (on a deny path) calls
`log_denial(policy, cap_name)`, which constructs:

```simple
val event = SecurityEvent.CapabilityDenied(
    capability: cap_name,
    window_id: policy.window_id
)
```

(`src/lib/common/ui/capability_policy.spl:243-246`). This construction fails
to resolve only under `bin/simple test`.

## Command

```
SIMPLE_RUST_SEED_WARNING=0 timeout 40 bin/release/x86_64-unknown-linux-gnu/simple test test/02_integration/app/ui.web/capability_gating_spec.spl --no-session-daemon
```

## Root-cause hypothesis

Same class as the two referenced landmine docs: the SSpec `test` evaluator
resolves imported symbols (here, an enum defined in one module and
constructed inside a *different* imported module's free function, several
call-frames removed from the spec file) through a different/incomplete
registration path than `bin/simple run`. Not confirmed here whether this is
the identical `impl_methods`/`GLOBAL_IMPL_METHODS` registration gap or a
distinct cross-module enum-variant-constructor resolution gap — the two
referenced docs are about `EnumName.static_method()` calls; this is about
`EnumName.Variant(...)` construction, so it may be a related-but-separate
code path. No Rust seed fix attempted here (out of scope; needs a rebuild).

## Not attempted

A `bin/simple run`-based repro was attempted but hit an unrelated error
(`CapabilityPolicy()` construction / `cannot iterate over this type`) before
reaching the `SecurityEvent.CapabilityDenied` construction line, so a clean
run-vs-test A/B on this exact construction was not completed. The `test`-path
failure itself is directly reproduced and unambiguous.

## Triage 2026-11-25 (work/p2w5-ai-20261125)

**Classification: SKIP (Rust-seed-only, verification environment-blocked).**

- The failing path is the Rust-seed SSpec `test` evaluator's cross-module
  enum-variant-constructor resolution. The bug doc itself records "No Rust
  seed fix attempted here (out of scope; needs a rebuild)"; the pinned seed
  binary (`bin/simple.exe`, v1.0.0-rc.1) cannot be rebuilt in this lane
  (no cargo/rust builds permitted).
- Re-running the named spec on 2026-11-25 is blocked repo-wide at
  release/1.0.0 HEAD: `bin/simple.exe test
  test/02_integration/app/ui.web/capability_gating_spec.spl --mode=interpreter`
  fails before collecting any example with
  `error: semantic: src/app/test_runner_new/test_runner_client.spl:9:1:
  unknown decorator '@representation_boundary'` — the source/binary
  inconsistency introduced by cfd89933699 (940 `@representation_boundary`
  annotations the pinned seed rejects).
- Code inspection confirms the bug's factual basis is unchanged: the
  `CapabilityDenied(capability: text, window_id: text)` variant still exists
  (`src/lib/nogc_sync_mut/security/types.spl:19`) and
  `src/lib/common/ui/capability_policy.spl:253` still constructs
  `SecurityEvent.CapabilityDenied(...)` inside the transitively-called free
  function, so the doc is not stale.
- Status remains `open`; re-verify once a self-hosted binary can run the
  spec (or the seed is rebuilt past the decorator support).
