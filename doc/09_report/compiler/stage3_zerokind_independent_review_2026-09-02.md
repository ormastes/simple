# Independent Stage 3 ZeroKind review (2026-09-02)

## Verdict

Structural PASS with runtime evidence pending. No restart, rebuild, or deploy was performed.

## Findings

- The preserved failure proves a well-formed `HirType` reached MIR lowering with a raw-zero `kind`; it does not prove where corruption originated.
- The historical `compile_specialized_template_release` suffix was a scope-list tail, not an active-function identity. Attribution to that function is rejected.
- The default-off probe captures owner-local active-function state and two-sided discriminants for parameter and return-type crossings. Nested lowering gets its own context. `recursive-or-other` intentionally narrows, but does not identify, body-level or recursive transport.
- `SIMPLE_MIR_TAG_PROBE=1` is accepted only by the fixed literal-value allowlist and is included in the same Stage 3 environment vector used by the invocation transcript and args digest.
- Full stderr prefers the provenance-bound cache. Spill allocation now advances past every existing PID/sequence path, preventing a later bounded print or recycled PID from overwriting retained evidence in the isolated cache.
- Restart remains unauthorized until the frozen source, newly admitted Stage 2 parent, isolated writable paths, probe-bearing args digest/transcript, immutable stderr copy, and no-deploy conditions in the root-cause report are satisfied.

## Evidence boundary

The next authorized probe run may distinguish an immediate signature crossing from earlier corruption. It cannot by itself establish a semantic ABI fix, and no source location should be named as root cause until the emitted caller/callee record supports it.

## Validation

- The production diagnostic-environment ablation and digest gate passed all six checks.
- Shell syntax and focused whitespace validation passed.
- SPipe execution was not claimed; this review intentionally did not run, rebuild, restart, or deploy a compiler.
