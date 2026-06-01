# System Test Plan: Harden TUI/GUI Layout Comparison

Status: selected scope. User approved Feature Option 3 and NFR Option C on 2026-06-01.

## Existing Executable Coverage

- `test/integration/rendering/backend_screenshot_compare_spec.spl`: compositor comparison semantics, invalid dimensions, profile path, and diff diagnostics.
- `test/system/wm_compare/html_compat_spec.spl`: HTML fixture manifest, Chrome golden loading, exact/perceptual policy, truncated buffers, and pair metadata mismatch.
- `test/system/wm_compare/emulated_capture_spec.spl`: deterministic capture failure and invalid viewport behavior.
- `test/system/wm_compare/site_corpus_pair_spec.spl`: famous-site pair metadata mismatch.
- `test/unit/lib/gpu/engine2d/backend_probe_strict_spec.spl`: backend evidence contract.

## Required Gates

- No executable `.spl` specs under `doc/06_spec`.
- No `pass_todo`, false-pass assertions, or placeholder-only scenarios in changed specs.
- Generated/manual scenario documents under `doc/06_spec` must explain the comparison policy without opening source specs.
- Focused specs must pass uncached after comparison/backend changes.

## Required Remaining Specs

- Add a structural layout comparison spec for TUI cell grids versus GUI/browser layout boxes.
- Add a mismatch report spec that proves capture failures, metadata drift, geometry drift, pixel drift, and backend unavailability are separate statuses.
- Add a measurement-spec or report verifier for warm startup, max RSS, and binary size delta.
- Add backend-qualified report checks for Metal, Vulkan, CUDA, and CPU SIMD lanes.

## Current Verification Commands

- `SIMPLE_LIB=src src/compiler_rust/target/debug/simple test test/integration/rendering/backend_screenshot_compare_spec.spl --mode=interpreter --clean`
- `SIMPLE_LIB=src src/compiler_rust/target/debug/simple test test/system/wm_compare/html_compat_spec.spl --mode=interpreter --clean`
- `SIMPLE_LIB=src src/compiler_rust/target/debug/simple test test/system/wm_compare/emulated_capture_spec.spl --mode=interpreter --clean`
- `SIMPLE_LIB=src src/compiler_rust/target/debug/simple test test/system/wm_compare/site_corpus_pair_spec.spl --mode=interpreter --clean`
- `SIMPLE_LIB=src src/compiler_rust/target/debug/simple test test/unit/lib/gpu/engine2d/backend_probe_strict_spec.spl --mode=interpreter --clean`
- `find doc/06_spec -name '*_spec.spl' | wc -l`
