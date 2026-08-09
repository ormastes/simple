# Authoring a capability library

**Status: skeleton (stream P1).** This covers only the critical-mode section
(design §10.2). P12 fills in the rest.

Design: `doc/05_design/app/tools/unified_debug_profile_capability_architecture_2026-08-09.md`

## What a capability group is

A capability group is **one trait over one value**: the literal union of its
member traits' method sets, which is exactly what the `with` sugar desugars to.

```simple
trait DebugProfiler with DebugTarget, ProfileTarget:
    pass
```

The implementing type implements all three traits — both members and the group
— all forwarding to one private implementation, and acquisition returns the
single value carrying both capabilities.

### Two rules you cannot get wrong

1. **A group is never a struct pairing two accessors.** Classes in this
   language are value types: `val b = a` copies. Pairing `session.debug()` with
   `session.profile()` gives you two independent copies, and stepping the debug
   half leaves the profile half at zero. This was measured RED before being
   corrected — see
   `doc/08_tracking/bug/capability_group_from_unsound_under_value_semantics_2026-08-09.md`.

2. **`me` versus `fn` on trait methods is load-bearing.** A `fn` method receives
   a *copy* of the receiver and silently discards any mutation; the compiler
   does not object. Every mutating method (`set_breakpoint`, `step`, `resume`,
   `attach`, `profile_begin`, `profile_end`, `shutdown`, …) must be declared
   `me`, and implementers must reproduce those markers verbatim.

## Critical mode

Critical mode is enabled per project in `config/critical_mode.sdn`:

```
critical:
  enabled: true
  dynamic_acquire: warn        # allow | warn | error
  gpu:
    backend: cuda(sm80)        # `auto` is rejected under critical mode
```

Read it with `std.critical.capability_manifest.load_critical_mode_config`.

### Acquire at boot, not in the loop

Acquire each capability once, in a function marked `@init_phase`, and pass the
value down. The `dynamic_capability_acquire` lint enforces this (DCA001); see
the [lint guide](../app/lint.md#dynamic-capability-acquisition-lint-dca001-dca002)
for the exact marking rules and the diagnostic text.

```simple
@init_phase
fn boot(src: Host) -> Option<DebugProfiler>:
    ref_debug_profiler(src)
```

`@init_phase` marks the function directly beneath it. A bare `@init_phase` at
the top of a file marks the whole module — the composition-root escape hatch,
so a module that exists only to wire the system up need not annotate every
function. The attribute does **not** propagate into callees; the lint is
syntactic and does not pretend to do reachability.

### Warning now, error later

`critical.dynamic_acquire` starts at `warn` in critical builds and is promoted
to `error` in a later release. Do not hard-code the severity anywhere; a
library that wants to be ready for the promotion should simply have no DCA001
findings under `warn` today.

### Pin the backend, and refuse on mismatch

Under critical mode the GPU backend is pinned in the manifest — `auto` is a
DCA002 error, because it defers the choice to a boot probe. At boot, call the
gate:

```simple
val check = verify_gpu_manifest_pin(cfg.gpu_backend, probe_backend(), cfg.enabled)
if not check.ok:
    print check.report
    return    # refuse to start
```

On mismatch the gate yields `ok: false` and a `REFUSING TO START` report naming
both the pinned and the probed backend. This is a promoted fault path, not a
fallback: it must never continue on the probed backend, because running code
paths the build was not validated against is precisely what the pin prevents.

## Reference

- Lint: `src/compiler/35.semantics/lint/dynamic_capability_acquire.spl`
- Config + boot gate: `src/lib/common/critical/capability_manifest.spl`
- Config file: `config/critical_mode.sdn`
- Landed group shape: `src/lib/common/debug/debug_profiler.spl`
