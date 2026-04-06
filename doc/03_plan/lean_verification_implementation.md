# Lean Verification Mode — Current Implementation State

**Version:** 2026-03-31
**Status:** Implemented infrastructure; supported end-to-end workflow still partial
**Specification:** [lean_verification_with_aop.md](../research/lean_verification_with_aop.md)

## Summary

Simple already ships real Lean verification infrastructure:
- an authoritative generated-artifact inventory
- Lean artifact regeneration via `simple gen-lean write --force`
- proof checking via `simple gen-lean verify`
- status and inventory entrypoints via `simple verify status` and `simple verify list`
- workflow-level tests for inventory reporting, regeneration helpers, and missing-artifact failure handling

What is still missing is a repo-default, evidence-backed, end-to-end verification story that can be advertised as complete from a clean checkout.

## Current Repo State

As of 2026-03-31, the repository truth is:
- Lean tooling exists, but a clean checkout does not ship the generated `verification/**/*.lean` outputs by default.
- `simple verify check` is a thin Lean-verification preflight and proof-check command. It forwards to `simple gen-lean verify`.
- `simple verify status` always reports Lean availability and whether the known generated artifacts exist.
- `simple verify list` prints the authoritative artifact inventory.
- `simple gen-lean verify` and `simple verify check` both fail fast when no supported generated Lean artifacts are present.
- The main evidence gap is workflow-level reproducibility on representative fixtures, not complete absence of implementation.

## Implemented Infrastructure

### Command surface

The current public command contract is:
- `simple verify status`: report Lean availability and generated-artifact presence
- `simple verify list`: print the authoritative Lean artifact inventory
- `simple verify regenerate`: regenerate tracked Lean files by forwarding to `simple gen-lean write --force`
- `simple verify check`: run the same proof-checking path as `simple gen-lean verify`
- `simple gen-lean write --force`: regenerate tracked Lean artifacts into `verification/`
- `simple gen-lean verify`: run Lean over supported generated artifacts and fail on errors or `sorry`

Primary implementation references:
- [verify.rs](src/compiler_rust/driver/src/cli/verify.rs)
- [gen_lean.rs](src/compiler_rust/driver/src/cli/gen_lean.rs)
- [main.spl](src/compiler/90.tools/verify/main.spl)

### Generated-artifact inventory

The authoritative inventory currently covers 15 tracked Lean outputs, including:
- `verification/nogc_compile/src/NogcCompile.lean`
- `verification/type_inference_compile/src/TypeInferenceCompile.lean`
- `verification/type_inference_compile/src/Contracts.lean`
- `verification/type_inference_compile/src/AsyncEffectInference.lean`
- `verification/type_inference_compile/src/Generics.lean`
- `verification/memory_capabilities/src/MemoryCapabilities.lean`
- `verification/memory_model_drf/src/MemoryModelDRF.lean`
- `verification/tensor_dimensions/src/TensorDimensions.lean`
- `verification/tensor_dimensions/src/TensorMemory.lean`

That inventory is defined in the Rust driver and shared by status, regeneration, and proof-checking.

### Test coverage already present

Current evidence in-tree:
- [lean_verify_cli_spec.spl](test/system/compiler/lean_verify_cli_spec.spl) verifies status/list output and the clean missing-artifact failure mode.
- [lean_verification_workflow_spec.spl](test/system/compiler/lean_verification_workflow_spec.spl) verifies regeneration helpers and proof-summary formatting.

## Gaps Before This Can Be Advertised As Complete

The remaining gaps are concrete:
- Generated Lean artifacts are absent in a clean checkout, so proof checking cannot succeed without a prior generation step.
- The repo does not yet demonstrate a stable documented end-to-end Lean verification flow on representative fixtures from generation through proof check.
- Public documentation has historically mixed “100% complete” claims with “still partial” caveats; those claims must stay aligned with the actual command behavior.
- Some historical docs still describe older path layouts or older ownership boundaries and should not be treated as the current public interface.

## Supported Workflow Today

The supported workflow today is:

```bash
simple verify status
simple verify list
simple gen-lean write --force
simple verify check
```

Expected clean-checkout behavior:
- `simple verify status` succeeds and reports that the tracked Lean artifacts are missing until generation is run.
- `simple verify check` fails with a preflight message when no supported generated files exist.
- `simple gen-lean write --force` generates the tracked outputs into `verification/`.
- `simple verify check` and `simple gen-lean verify` then operate on the generated files.

## Acceptance Criteria For “Complete”

Lean verification should remain classified as partial until the repo shows all of the following:
- a reproducible fixture-backed generation and proof-check workflow from a clean checkout
- passing end-to-end proof validation on representative generated artifacts
- aligned CLI help, README messaging, and implementation docs
- no conflicting “complete” claims that exceed the actual verified workflow
