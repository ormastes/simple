# Linker spill-frame extent overflow

Status: corrected; production verification blocked. Owner: Codex items_4_5.

`src/lib/nogc_async_mut/link_working_set/spill.spl` validates payload length and
CRC but does not check whether `logical_offset + payload_bytes` is representable
as `u64`. A nonempty frame at the maximum offset currently passes integrity
validation even though its exclusive output end overflows.

Acceptance: reject overflowing extents before accepting their checksums;
preserve exact-boundary extents and empty frames. Traceability: mold linker
design section 8 staged-range integrity and plan G3 bounded spill. This does not
establish whole-job memory accounting or host linker admission.

Use the existing planner SSpec with actual production constructors/validator,
record red before the pure-Simple correction, and cover the adjacent exact
boundary and empty cases. Phase 1 results are diagnostic only; production
verification remains blocked on an admitted runtime.

## Test-first diagnostic evidence

Windows Phase 1 interpreter, 2026-09-29: before correction the focused SSpec
executed six examples, passed five, and failed the exact maximum-offset
regression (`expected true to equal false`), process exit 1. After adding the
checked-subtraction extent guard, the same six examples passed with zero
skips/drops and process exit 0. Adjacent exact-boundary and empty cases passed;
the existing payload corruption/truncation cases remain covered.

Logs: `build/native_probe/link-spill-integrity/red.log` and `green.log`.
The runtime is the explicitly authorized Windows Stage 1 seed with SHA-256
`6456107ce86e91d06a03171873b141632b819b8a59637f9fab414e0dcee0dae6`.
This is diagnostic evidence, not self-hosted or Windows/Linux linker admission.
Phase 1 `spipe-docgen` generated the mirrored planner manual with one complete
document and zero stubs (exit 0); the three new scenarios and imperative steps
were inspected. This generation carries the same diagnostic runtime limitation.
Remaining unblock condition: repeat the focused scenario with an admitted
self-hosted runtime, regenerate its manual, and complete required core checks.
