# Kernel Plugin Fabric Acceptance Test Plan

Status: executable acceptance scaffolding; runtime scenarios are intentionally
in development until the production KPF modules land.

## Scope and pass criteria

The Wave 0 shell checker parses a versioned closure descriptor, requires a
non-empty set of roots and source files, and rejects every import outside the
allowlisted K0g prefixes. Its self-test must accept a clean fixture and reject
an escaped import, malformed descriptor, and zero-file closure.

The SPipe runtime suite calls only the future production acceptance facade
`std.nogc_async_mut.kernel_plugin.acceptance`; it does not contain a second
runtime model. PASS requires all five scenarios to execute with a nonzero
authoritative result count. An unresolved facade, dropped scenario, timeout,
or summary-free exit is not PASS.

## Execution order

1. `sh scripts/check/kernel-plugin-fabric/check-k0g-import-closure.shs --selftest`
2. `sh scripts/check/kernel-plugin-fabric/check-k0g-import-closure.shs`
3. `bin/simple test test/03_system/compiler/feature/kernel_plugin/k0g_import_closure_spec.spl --tag in-development --no-session-daemon`
4. `bin/simple test test/03_system/compiler/feature/kernel_plugin/kernel_plugin_fabric_acceptance_spec.spl --tag in-development --no-session-daemon`

The two specs retain `@tag:in-development` while their production roots/facade
are absent. Remove the tag and tracking line in the implementation commit that
makes each spec pass. Do not convert absence to a skip.

## Traceability

| Requirement | Executable evidence | Non-vacuous oracle |
|---|---|---|
| REQ-KPF-002 | `k0g_import_closure_spec.spl`; K0g checker | positive fixture plus three deliberate-red cases; nonzero production file count |
| REQ-KPF-004 | `kernel_plugin_fabric_acceptance_spec.spl` | exact malformed-descriptor code and generation remains unpublished |
| REQ-KPF-009 | same | requested checks positive, completed zero, verdict exactly `INCOMPLETE` |
| REQ-KPF-005/007 | same | third enqueue is `WouldBlock`, capacity/high-water fixed at two |
| REQ-KPF-007 | same | reused slot has generation 2; old handle errors while current handle succeeds |
| REQ-KPF-001 | same | both adapters call distinct providers once and equal the absolute `[6, 10, 16]` oracle |

## Exclusions and evidence policy

This lane does not implement KPF, edit production source, generate ABI bindings,
or claim native/worker/Wasm parity. The scenarios are operator-facing textual
evidence; no raster capture is applicable. Generated manuals are deferred to
the docgen owner because this lane is restricted from `doc/06_spec/**`.
