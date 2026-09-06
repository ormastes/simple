# Proton/Wine fixture specs assert an API shape that no longer exists — needs product decision, not a mechanical fix

**Date:** 2026-07-20
**Severity:** low (test-only; both are `lib/common` fixture/evidence
scaffolding for a not-yet-shipped Proton/Wine feature)
**Status:** open — classification only, no fix attempted
**Found by:** whole-suite `test/unit/` triage campaign, `lib/common`
cluster

Two unrelated specs both fail because they were written against an evidence/
constructor API shape substantially different from (richer than) what
currently exists in source. In both cases this is NOT a mechanical rename —
picking a fix requires deciding which side (test's richer intended design, or
source's simpler current implementation) is authoritative, which is a
product/design call, not a triage-scope edit. Left unmodified per the "never
weaken/rewrite an assertion to force green" rule.

## 1. `test/unit/lib/common/wine_hello_fixture_spec.spl` (1 failure)

Spec imports/calls:
```simple
use common.wine_hello_exe.{wine_hello_exe_probe, wine_hello_exe_can_execute}
use common.wine_hello_fixture.{wine_known_hello_exe_fixture_bytes, wine_hello_fixture_verified_gates}
...
val result = wine_hello_exe_probe(wine_known_hello_exe_fixture_bytes(), wine_hello_fixture_verified_gates())
expect(result.status).to_equal("executed")
expect(result.stdout).to_equal("Hello from SimpleOS Wine\n")
expect(result.stdout_handle).to_equal(-11)
expect(result.bytes_written).to_equal(25)
expect(result.exit_code).to_equal(0)
expect(wine_hello_exe_can_execute(...)).to_equal(true)
```

Current source (`src/lib/common/wine_hello_exe.spl`,
`src/lib/common/wine_hello_fixture.spl`):
- No `wine_hello_exe_probe` (2-arg), only
  `wine_hello_exe_probe_manifest_evidence_vm(exe_bytes, precondition_manifest,
  execution_evidence, space: WineVmProcessSpace, load_addr, stack_addr,
  heap_size, stack_size)` — 8 args including a `WineVmProcessSpace` object
  and explicit VM memory addresses.
- No `wine_hello_exe_can_execute` at all.
- `WineExeProbeResult` (the actual return type) has `status`/`error`/
  `stdout`/`exit_code` fields only — no `stdout_handle` or `bytes_written`.
- No `wine_hello_fixture_verified_gates()`; closest analogues are
  `wine_hello_fixture_precondition_manifest()` and
  `wine_hello_fixture_execution_evidence_struct()`.

Fixing this requires constructing a valid `WineVmProcessSpace` fixture and
deciding whether to drop the `stdout_handle`/`bytes_written` assertions
(which would violate the "never weaken an assertion" rule) or whether those
fields are a still-missing feature gap in `WineExeProbeResult`.

## 2. `test/unit/lib/common/proton_session_spec.spl` (3 of 4 failures)

Spec calls:
```simple
val evidence = proton_non_wine_runtime_evidence_new(
    "steam-runtime abi-x86_64 soldier",
    "pressure-vessel-container container-rootfs ... namespace-capability",
    "vulkan-loader vulkan-device dxvk",
    "proton-launcher steamworks-bridge controller-input",
    "esync-or-fsync"
)
```

Current source (`src/lib/common/proton_runtime_subsystems.spl`): no
`proton_non_wine_runtime_evidence_new` function exists at all. The actual
class is:
```simple
class ProtonNonWineRuntimeEvidence:
    pressure_vessel: bool
    container_rootfs: bool
    namespace_pid: bool
    namespace_fs: bool
    namespace_ipc: bool
    namespace_net: bool
    namespace_capability: bool
    runtime_version: text

    static fn new(runtime_version: text) -> ProtonNonWineRuntimeEvidence   # 1 arg
    static fn all_verified(runtime_version: text) -> ProtonNonWineRuntimeEvidence  # 1 arg
```
— 7 boolean subsystem flags + a version string, constructed via a 1-arg
`.new(runtime_version)`/`.all_verified(runtime_version)`, not the 5
free-text-string constructor (steam-runtime / pressure-vessel / vulkan /
proton-launcher / sync-mode detail strings) the spec expects. The spec's
"blocks session planning on incomplete ... evidence" and "plans a launch
session when every ... subsystem is ready" examples assert on richer
per-subsystem detail-string content (`to contain "esync-or-fsync"`, `to
contain "vkd3d-proton"`) that the current boolean-only evidence model has no
way to represent.

Same call as above: deciding whether `ProtonNonWineRuntimeEvidence` should
be redesigned to carry detail strings (matching the spec's intent) or the
spec should be rewritten to the boolean-flag model is a design decision.

## Affected

- `test/unit/lib/common/wine_hello_fixture_spec.spl` — 1/1 example.
- `test/unit/lib/common/proton_session_spec.spl` — 3/4 examples (the 4th,
  `"rejects incomplete session requests before runtime evidence"`, only
  exercises `proton_session_request_new`/`proton_session_request_gate`,
  which DO match current source, and passes).
