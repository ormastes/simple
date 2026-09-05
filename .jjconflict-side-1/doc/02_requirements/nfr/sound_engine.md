<!-- codex-research -->
# Sound Engine NFR Requirements

## Selection
User selected NFR option `3`: Full Cross-Platform Production Targets.

## Targets
- NFR-001: Platform evidence must cover Linux, BSD, macOS, Android, iOS, and Simple OS with `native`, `portable`, `unsupported`, or `host-unavailable` status recorded per target.
- NFR-002: Host-unavailable evidence is acceptable only when the current host cannot execute a target; the evidence must name the missing host, emulator, device, or driver condition.
- NFR-003: The no-audio backend must run deterministically in CI and must not require native audio hardware, GUI, or renderer availability.
- NFR-004: Mixer command ordering must be deterministic across inline and worker-backed execution paths.
- NFR-005: Codec parsing must reject malformed input without unbounded allocation, unchecked frame sizes, or success-by-empty-output behavior.
- NFR-006: Codec and DSP hot paths must include baseline and optimized measurements, and any failure to approach intended C/JS-class performance must be recorded as a concrete blocker or bug.
- NFR-007: Parallel worker evidence must prove whether runtime pool execution was used or an inline fallback was selected; fallback must not masquerade as CPU-parallel work.
- NFR-008: The public sound layer must stay lightweight: production entrypoints may use cached/native runtime artifacts for device I/O, but public Simple APIs must not import test/debug-only surfaces.
- NFR-009: SPipe specs must avoid placeholder passes, empty bodies, boolean-wrapper placeholder assertions, and equality-only checks where both sides can share the same flawed producer.
- NFR-010: Generated manuals under `doc/06_spec` must be readable scenario manuals for the primary sound-engine flows, and executable `.spl` specs must remain under `test/`.
- NFR-011: The lane must include a reviewer handoff checklist that separates research, design, implementation, codec, optimization, platform, hardening, and documentation evidence.
