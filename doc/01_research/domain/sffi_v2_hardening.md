<!-- codex-research -->
# Domain Research: SFFI v2 Hardening

**Date:** 2026-08-21
**Canonical synthesis:** `doc/01_research/platform/sffi_v2_hardening_2026-08-21.md`

This companion preserves the external reasoning behind the selected SFFI v2
architecture. It references the supplied synthesis rather than duplicating it.

## Findings

1. Rust treats foreign declarations as unsafe because a compiler cannot verify
   the foreign definition. Checked lifting (`NonNull::new`) establishes a
   narrower invariant; annotations do not.
2. C/C++ nullability annotations improve diagnostics, but attributes such as
   `returns_nonnull` can become optimizer assumptions. Runtime contract checks
   remain necessary unless an exact proof-backed policy permits elision.
3. ACSL/Frama-C WP, CBMC, and Kani discharge scoped obligations under explicit
   models, assumptions, and bounds. Sanitizers, Miri, and fuzzing exercise other
   defect classes. No one receipt means “arbitrary foreign code is safe.”
4. RustBelt, FFIChecker, and MiriLLI reinforce that safety must be re-established
   at the boundary, including ABI, initialization, aliasing, lifetime, and
   allocator assumptions—not nullability alone.
5. The WebAssembly Component Model demonstrates typed canonical lift/lower for
   options, results, lists, strings, and resources instead of integer-shaped
   generic marshalling.
6. SLSA and Sigstore distinguish exact subject identity/provenance from semantic
   correctness. SFFI therefore needs both executable contracts and signed exact
   artifact/build evidence.
7. Git LF normalization reduces checkout variance, but security identity must
   independently classify text/binary inputs and hash length-framed canonical
   source plus exact compiler inputs and artifact bytes.

## Selected direction

The user selected a versioned stable C ABI shim, unsafe generated raw binding,
generated validation/lift wrapper, and safe `T`/`Option`/`Result` API. Checks
remain enabled by default. Unverifiable in-process providers remain unsafe or
are isolated behind a validated process/Wasm protocol.

Primary references and URLs are maintained in the canonical synthesis.
