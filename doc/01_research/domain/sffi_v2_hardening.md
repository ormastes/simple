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

## Current-tree census update — 2026-08-25

The canonical fail-closed census was rerun after the broad SFFI authority
migration. It found 11,590 `rt_*` declaration rows representing 3,137 distinct
symbols. Only 2,826 rows / 1,779 symbols carry explicit lexical FFI-unsafe
tagging; 8,515 rows / 1,825 symbols remain wholly untouched. No complete
evidence bundle was supplied, so evidence-verified, signature-verified, and
verified-and-signed counts are all zero. There are 263 distinct symbols with
multiple source-signature hashes. These are ABI-triage candidates, not 263
proven machine-ABI conflicts: the source scanner can distinguish parameter
spelling or nullable syntax that resolves to the same calling convention.

Provider provenance is: 1,286 linked-native-language-unknown, 984 with no
implementation observed, 623 Rust, and 244 C-or-C++ source-only symbols. The
independent implementation scan found 2,405 C, 2,146 Rust, 687 Simple, and 219
C++ definitions. See `doc/09_report/sffi_safety_census_2026-08-25.md` for the
scope and interpretation.

This evidence contradicts any claim that all SFFI is safe or signed. The next
research slice must reconcile the 263 signature variants against compiler-
resolved canonical types first, then reduce
production untouched families (`rt_file`, `rt_process`, `rt_env`, `rt_time`,
`rt_dir`) through canonical typed owners. Signing remains a separate exact-
artifact admission property and must never be inferred from source annotations.
