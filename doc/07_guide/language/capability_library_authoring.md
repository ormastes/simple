# Authoring a capability library

How to write a backend that is debug-capable, profile-capable, or both, against
the traits that landed in `src/lib/common/debug/`. The worked example
throughout is the debug/profile capability itself — every rule below was paid
for by a measured RED in that work.

**Read the hazards section first.** It is not background; it is the reason
three separate streams shipped code that compiled, type-checked, and silently
did nothing.

Design (authoritative, and its §3 CORRECTION block overrides the prose beneath
it): `doc/05_design/app/tools/unified_debug_profile_capability_architecture_2026-08-09.md`

## Honesty preamble — what is actually proven

Everything documented here was measured under the **Rust seed**. No result in
this feature has self-hosted evidence. Where a mechanism is landed but
unreachable, this guide says so rather than describing the intent.

| Claim | Status |
|---|---|
| Host debug + profile targets | Run, measured |
| CUDA / Vulkan device debug + profile | Run on real device (20 launches each, field diffs clean) |
| Metal device path | **Unverified.** `svmg_metal_kernel.metal` has never been compiled by any Metal compiler — no `xcrun`/`metal` exists on the Linux dev host. Highest-risk unknown in the feature. Do not read the Metal wrapper's green specs as device evidence. |
| Trait-header `with` sugar | Landed and **inert** — see below |
| `.spl` → SVM-G GPU attach | Does not exist; DAP GPU attach is routing-only |

---

## The one hazard: assume every handle you hold is a copy

Classes in this language are **value types**. `val b = a` copies. There is no
compiler diagnostic anywhere in this area, so every symptom below presents as
"this backend can't profile" rather than as an error.

It reads as three separate traps. It is one:

### 1. Pairing diverges copies

A group built by pairing two accessors — `session.debug()` **and**
`session.profile()` — holds two independently diverging copies of the session.
Stepping the debug half leaves the profile half reading zero steps.

Measured by P2 as 8/70 RED, `expected 6, got 0`, before the shape was
corrected. Writeup:
`doc/08_tracking/bug/capability_group_from_unsound_under_value_semantics_2026-08-09.md`.

A group is **one trait over one value** — the literal union of its members'
method sets, acquired through a **single** accessor. Never a struct pairing two.

### 2. `fn` discards mutation

A `fn` trait method receives a **copy** of the receiver and silently discards
every mutation. The compiler does not object.

Every mutating method must be declared `me`. In the landed traits that is
`attach`, `debug`, `profile`, `shutdown`, `set_breakpoint`, `clear_breakpoint`,
`breakpoints`, `step`, `resume`, `state`, `read_mem`, `detach`, `profile_begin`,
`profile_end`. The `me` markers in the design doc and in
`src/lib/common/debug/*.spl` are **normative, not stylistic** — reproduce them
verbatim.

Caveat established by P3/P4/P9 and worth knowing so you don't chase it: it does
**not** bite for class-typed fields. That is a narrow exemption, not a licence —
`me` remains the correct default for anything that mutates.

### 3. Acquisition position decides aliasing

A capability handle **stops aliasing its target unless the acquisition is a
function's TAIL expression.** Bind it to a local, or inline it into a
constructor call, and the handle half-dies: `step`/`resume` keep working
through the target's class-typed sub-object, while `set_breakpoint` and
`profile_begin` are silently discarded.

Isolated by P10 with a 12-shape probe matrix. The container is irrelevant —
only syntactic position matters — and write-back does not fix it. Filed:
`doc/08_tracking/bug/ref_debug_profiler_handle_stops_aliasing_unless_tail_expression_2026-08-09.md`.

### Shapes proven safe in practice

Use one of these. Do not invent a fourth without a probe matrix.

- **Hold a class-typed session field directly** (P3, P9, P8).
- **Drive `launch()` without binding a handle at all** (P6, N3).
- **Return the acquisition as a function's tail expression:**

```simple
@init_phase
fn boot(src: RefDebugSession) -> Option<DebugProfiler>:
    ref_debug_profiler(src)          # tail expression — aliases
```

```simple
# BROKEN — binds to a local, handle stops aliasing
val dp = ref_debug_profiler(src)
dp.set_breakpoint(4)                  # silently discarded
```

---

## Anatomy of the landed capability library

`src/lib/common/debug/`:

| File | Contents |
|---|---|
| `capability.spl` | `CapLevel` (`Native`/`Emulated`/`Unavailable`), `cap_level_name`, `cap_level_from_name`, `cap_level_is_usable` |
| `session_core.spl` | `AttachOpts`, `DebugSessionCore` trait, `attach_is_ok`/`_skip`/`_error` |
| `debug_target.spl` | `DebugState`, PC/stop-reason constants, `DebugTarget` trait |
| `profile_target.spl` | `ProfileReport`, `PROFILE_ABSENT`, `ProfileTarget` trait, report helpers |
| `debug_profiler.spl` | `DebugProfiler` group trait (union of the two), `dp_trace_run` |
| `host_profile_target.spl` | `HostProfileTarget` — the reference host implementation |
| `ref_debug_session.spl` | `RefDebugTarget`/`RefDebugSession` — the reference VM, and the conformance oracle |

### Core trait vs enhanced trait vs group

- **Core trait** — the minimum a backend must answer. Accessors live here:
  `kind()`, `debug_level()`, `profile_level()` are plain `fn` because they read
  and do not mutate.
- **Enhanced trait** — additional methods a *capable* backend offers. Do not
  push an optional method onto the core trait and have half your backends
  return a sentinel; that is what `CapLevel` is for.
- **Group** — the union, one trait over one value, zero new methods:

```simple
trait DebugProfiler with DebugTarget, ProfileTarget:
    pass
```

**Accessor rule: accessors live on the core trait.** A group never introduces an
accessor, because an accessor on a group is exactly the pairing that diverges.

### CapLevel honesty rules

`CapLevel` is a claim about what your implementation actually did, not about
what the backend theoretically supports.

- `Native` — a real device/hardware mechanism produced the number.
- `Emulated` — the interpreter or a software model produced it.
- `Unavailable` — nothing produced it.
- `cap_level_name` is **lowercase**: `"native"`, not `"Native"`.

For profiling, `PROFILE_ABSENT = -1` is the **only** honest "not measured"
value. Reporting `0` is a contract violation — P7 found and fixed exactly that
in a landed `profile_end`. Use `profile_report_unavailable(detail)` rather than
hand-building a zeroed report, and use `profile_has_device_time` /
`profile_has_steps` before charting anything.

### Landed contract details the design doc does not specify

Match these exactly; the conformance vectors assert them.

- `set_breakpoint` returns **false when the breakpoint is already present**. It
  is not idempotent-true.
- `breakpoints()` returns **ascending** order.
- `read_mem` returns an **empty** array on overrun, never a short buffer.
- Profiling must be **armed at attach** via `AttachOpts.profile`. GPU PROF-1
  cannot be enabled after upload, so there is no "start profiling later".
- `AttachOpts` fields: `step_budget`, `entry_pc`, `log_cap`, `profile`.
  Constructors: `attach_opts_default()`, `attach_opts_with_budget(budget)`.

### Naming the accessor

Until the `with` sugar becomes reachable, each backend supplies its own
single accessor named `<backend>_debug_profiler(session)`:

- `ref_debug_profiler` (`src/lib/common/debug/ref_debug_session.spl`)
- `cuda_debug_profiler` (`src/lib/gc_async_mut/gpu_lane/cuda_debug_session.spl`)
- `vulkan_debug_profiler` (`src/lib/gc_async_mut/gpu_lane/vulkan_debug_session.spl`)
- `metal_debug_profiler` (`src/lib/gc_async_mut/gpu_lane/metal_debug_session.spl`)

The `dynamic_capability_acquire` lint recognises this naming
(`_dca_scan_debug_profiler`), so an off-pattern name loses lint coverage.

---

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

### A capability check would fail OPEN under native codegen

`if val` is broken in the AOT lane: a real `nil` binds as `SOME` under
`native-build`. So a generated capability check of the form
`if val cap = maybe_capability(): …` would take the present branch on an absent
capability. Nothing wires that generated check today, but do not add one until
the `if val` defect is fixed — the failure mode is fail-open, which is the worst
possible direction for a capability gate.

---

## The trait-header `with` clause is INERT

> **Do not document, teach, or rely on this sugar as available.**

`trait DebugProfiler with DebugTarget, ProfileTarget:` parses, and a desugar
exists. Neither reaches your code:

1. **`desugar_traits` is not on any compile path.** It lives in
   `src/app/desugar/trait_desugar.spl` — a **text-level, pre-parse** transform.
   Its only caller in the tree is `src/app/desugar/mod.spl:210`, inside the
   standalone `app.desugar` tool. The compiler deliberately does not import
   `app.desugar` (see the layering note at
   `src/compiler/20.hir/hir_forward_lowering.spl:33-35`), so no compilation of
   ordinary source ever runs it.
2. **The deployed seed predates the parser change.** Even if the desugar were
   wired, the binary you are running today would not accept the syntax.

`src/lib/common/debug/debug_profiler.spl` therefore spells the group out
longhand — all fourteen methods, duplicated from the two member traits — and
carries a comment saying why. Match that pattern. When the sugar becomes
reachable, the longhand form is exactly what it will desugar to, so nothing
breaks.

This is a live instance of a broader problem: see "a green spec says nothing
about reachability", below.

---

## Testing practice — required reading

This feature exposed a systemic weakness in how the repo's specs are written.
Every item below is a real failure from these streams, not a hypothetical.

### Assert on execution, not on text or structure

P0's generator passed **21/21** while emitting code that could not compile. The
specs asserted on the shape of generated text. Nothing ran it.

If your subject produces code, the spec must **execute** the product. If it
produces a report, assert on values the report only holds when work happened.

### A disjunctive spec is unfalsifiable

"skips cleanly **OR** matches `ref_vm`" proves nothing — it is green on a host
with no device, green on a host with a device, and green if the executor is
deleted.

Specs must **emit which branch ran** and support forcing:

```
DEVICE-RAN: cuda 20 launches
SKIPPED: no cuda driver — the DEVICE-RAN branch did NOT run
```

- Print the branch marker, and support `SIMPLE_REQUIRE_GPU=1` to turn a skip
  into a failure.
- **`step()` text is SWALLOWED on passing runs.** Use `print` or put the
  information in the assert message — found independently by N3 and P13, which
  is how much time it costs.

### Prove your oracle by sabotage

An oracle you have not tried to break is a guess.

- P6b proved real device runs with a **launch-count floor** — the sabotage read
  `expected 20 to be greater than 100000`, which is what a real oracle looks
  like when you break it.
- P4 caught its own zero-overhead oracle **passing with the guards removed**,
  and fixed the oracle rather than the guard.

### Gate tautologies

P15 found **12 specs** whose only assertion was
`test_env_require(...) == "blocked:..."`. They were green *because* the gate was
shut, and carried **false `@cover` claims** for behaviour they never touched.

> **The fix is NOT flipping the expected value to `ready`.** That trades one
> vacuous spec for another — it just asserts the gate is open instead of shut,
> and still exercises nothing. A gated spec must assert on **behaviour behind
> the gate** when the gate is open, and must not claim `@cover` for anything it
> cannot reach when the gate is shut.

### A green spec says nothing about reachability

Three mechanisms landed in this repo are fully implemented, fully specced,
green — and have **no caller**:

- `desugar_traits` (above)
- `svmg_lowering` — `lower_svmg_program` has no caller outside `70.backend`
- `action_key` / `interface_digest` — deliberately "compute-and-log only"

Before claiming a mechanism works end to end, grep for its callers. A spec
proves the function; only a caller proves the feature.

---

## Reference

- Traits and reference implementations: `src/lib/common/debug/`
- GPU wrappers: `src/lib/gc_async_mut/gpu_lane/{cuda,vulkan,metal}_debug_session.spl`
- Lint: `src/compiler/35.semantics/lint/dynamic_capability_acquire.spl`
- Config + boot gate: `src/lib/common/critical/capability_manifest.spl`
- Config file: `config/critical_mode.sdn`
- DAP surface: [`../app/lsp_dap/debug_profile_dap.md`](../app/lsp_dap/debug_profile_dap.md)
- Grammar (inert sugar): [`../quick_reference/syntax_quick_reference.md`](../quick_reference/syntax_quick_reference.md)
- Feature-expert hub: `doc/00_llm_process/feature_expert/debug_profile/skill.md`
