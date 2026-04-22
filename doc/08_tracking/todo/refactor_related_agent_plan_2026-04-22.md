# refactor_related_agent_plan

Date: 2026-04-22
Scope: refactor-related TODO rows 11, 12, 194, 195 plus malformed rows 147 and 148

## Assignments

- Semantic-token duplicate rows: assigned to Jason for research. Result: rows 11 and 12 are stale duplicate path entries from symlinked app paths; close in tracking only.
- Placeholder backlog: assigned to Peirce for research. Result: burn down `test/system/compiler/symbol_analysis_spec.spl` first; parent row 194 remains open.
- JS runtime guest instrumentation: assigned to Anscombe for research. Result: feasible as a small probe/instrumentation task, but real runtime fix may expand beyond one file.
- Malformed parser-spec rows: handled locally. Result: escape scanner examples and update legacy assertions in the touched spec.

## Row 195 Plan

`js_runtime_guest_001` should remain open until QEMU-backed evidence is added. The next implementation step is:

1. Add gated serial logging in `examples/simple_os/arch/x86_64/boot/baremetal_stubs.c` around `rt_array_push`, including array pointer, heap type, length, capacity, and growth-path state.
2. Add or extend an isolated JS runtime probe entry near `examples/simple_os/arch/x86_64/js_runtime_probe_entry.spl` with phase markers around `JsRuntime.new()` and `eval()`.
3. Tighten `test/system/js_runtime_in_qemu_spec.spl` to require the new markers when the QEMU lane runs.
4. Validate with `bin/simple test test/system/js_runtime_in_qemu_spec.spl` and `bin/simple test test/system/browser_runtime_in_qemu_spec.spl`.

Risk: instrumentation can perturb guest timing or heap layout, so the probe should be low-volume and gated. If the probe still fails in object or environment storage, the real fix likely belongs in the JS runtime implementation rather than the C stubs.

## Completed Fixes

- Rows 11 and 12 closed as duplicate semantic-token path rows.
- Rows 147 and 148 closed as malformed scanner artifacts.
- Row 194 received one concrete placeholder burn-down in `test/system/compiler/symbol_analysis_spec.spl`; parent tracker remains open.
