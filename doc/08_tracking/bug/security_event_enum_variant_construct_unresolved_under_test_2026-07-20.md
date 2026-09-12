# `EnumName.Variant(named_args)` construction unresolved under `bin/simple test` (via transitively-called free fn)

- **Date:** 2026-07-20
- **Status:** CLOSED (2026-09-12) — fixed in source (import pinned to the common tier); spec green on seed `3d120a6f`
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

## Re-check 2026-09-12 (BUGFIX-5)

Binary: `/home/yoon/dev/simple/bin/release/aarch64-unknown-linux-gnu/simple`
(Rust bootstrap seed, sha256 `3d120a6f`), worktree `/home/yoon/dev/simple-bugfix-5`
at base `89c5e3f865d`.

```
$ bin/simple test test/02_integration/app/ui.web/capability_gating_spec.spl --no-session-daemon
  ✓ default-deny policy denies InputInject
  ✓ granting InputInject allows it
SPEC FILE VERDICT: ... outcome=OK declared>=6 executed=6 passed=6 failed=0 skipped=0 dropped=0
```

This is not merely "stopped reproducing" — the defect was **fixed in source**
and the fix is self-documenting. `src/lib/common/ui/capability_policy.spl:8-17`
now carries an explicit note that `std.security.types` is ambiguous (both
`src/lib/common/security/types.spl` and `src/lib/nogc_sync_mut/security/types.spl`
declare `enum SecurityEvent`, and same-named enums from different modules
collapse in the global registry), so the import is pinned:

```simple
use std.common.security.types.{SecurityEvent, AuditEntry, AuditConfig}
```

and `log_denial` (`:252-256`) constructs `SecurityEvent.CapabilityDenied(
capability:, window_id:)` unchanged. So the root cause was not the `test`
evaluator failing to resolve a variant construction, as the record's "Area"
line guessed — it was an ambiguous module path resolving to the sibling
`SecurityEvent` that has no `CapabilityDenied` variant. Worth carrying forward
to the two sibling records this one cites, which may share that cause.

Closing.

- Status: CLOSED (2026-09-12) — fixed in source, verified on seed sha256 3d120a6f, 53bb6a16a5e, spec test/02_integration/app/ui.web/capability_gating_spec.spl
