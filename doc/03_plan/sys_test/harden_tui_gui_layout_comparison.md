# System Test Plan: Harden TUI/GUI Layout Comparison

Status: selected scope. User approved Feature Option 3 and NFR Option C on 2026-06-01.

## Existing Executable Coverage

- `test/integration/rendering/backend_screenshot_compare_spec.spl`: compositor comparison semantics, invalid dimensions, profile path, and diff diagnostics.
- `test/system/wm_compare/html_compat_spec.spl`: HTML fixture manifest, Chrome golden loading, exact/perceptual policy, truncated buffers, and pair metadata mismatch.
- `test/system/wm_compare/emulated_capture_spec.spl`: deterministic capture failure and invalid viewport behavior.
- `test/system/wm_compare/site_corpus_pair_spec.spl`: famous-site pair metadata mismatch.
- `test/system/wm_compare/structural_layout_report_spec.spl`: shared structural layout report contract, TUI cell geometry, GUI/browser layout boxes with stable node labels, geometry mismatch diagnostics, backend evidence links, pixel links, and focused famous-site layout-report attachment.
- `test/system/wm_compare/comparison_failure_report_spec.spl`: shared failure-triage contract separating capture failure, metadata drift, geometry drift, pixel drift, and backend unavailability.
- `test/system/wm_compare/backend_measurement_report_spec.spl`: backend-qualified timing/RSS/size evidence contract, binary-size delta reporting, required Metal/Vulkan/CUDA/CPU SIMD lane matrix, scalar-baseline requirement, and fallback rejection for accelerated lanes.
- `test/system/wm_compare/backend_measurement_capture_spec.spl`: host `/usr/bin/time` sample parsing into p50/p95, max RSS, binary-size, and backend measurement records.
- `test/unit/lib/gpu/engine2d/backend_probe_strict_spec.spl`: backend evidence contract.

## Required Gates

- No executable `.spl` specs under `doc/06_spec`.
- No `pass_todo`, false-pass assertions, or placeholder-only scenarios in changed specs.
- Generated/manual scenario documents under `doc/06_spec` must explain the comparison policy without opening source specs.
- Focused specs must pass uncached after comparison/backend changes.

## Remaining Verification Work

- Keep the focused verification command set below current when comparison/backend evidence code changes again.
- Keep the full famous-site corpus timeout tracked separately in `doc/08_tracking/bug/famous_site_corpus_full_spec_timeout_2026-06-01.md`; focused pair and structural corpus specs cover the hardened comparison contract in this change.

## Latest Focused Verification Evidence

2026-06-01 focused pass:

- `backend_screenshot_compare_spec.spl`: 9 passed.
- `html_compat_spec.spl`: 17 passed.
- `emulated_capture_spec.spl`: 5 passed.
- `site_corpus_pair_spec.spl`: 1 passed.
- `structural_layout_report_spec.spl`: 7 passed.
- `comparison_failure_report_spec.spl`: 5 passed.
- `backend_measurement_report_spec.spl`: 6 passed.
- `backend_measurement_capture_spec.spl`: 3 passed.
- `backend_probe_strict_spec.spl`: 8 passed.
- `find doc/06_spec -name '*_spec.spl' | wc -l`: `0`.
- Touched executable placeholder scan for `pass_todo`, false-pass assertions, and placeholder-only markers: no matches.

## Current Verification Commands

- `SIMPLE_LIB=src src/compiler_rust/target/debug/simple test test/integration/rendering/backend_screenshot_compare_spec.spl --mode=interpreter --clean`
- `SIMPLE_LIB=src src/compiler_rust/target/debug/simple test test/system/wm_compare/html_compat_spec.spl --mode=interpreter --clean`
- `SIMPLE_LIB=src src/compiler_rust/target/debug/simple test test/system/wm_compare/emulated_capture_spec.spl --mode=interpreter --clean`
- `SIMPLE_LIB=src src/compiler_rust/target/debug/simple test test/system/wm_compare/site_corpus_pair_spec.spl --mode=interpreter --clean`
- `SIMPLE_LIB=src src/compiler_rust/target/debug/simple test test/system/wm_compare/structural_layout_report_spec.spl --mode=interpreter --clean`
- `SIMPLE_LIB=src src/compiler_rust/target/debug/simple test test/system/wm_compare/comparison_failure_report_spec.spl --mode=interpreter --clean`
- `SIMPLE_LIB=src src/compiler_rust/target/debug/simple test test/system/wm_compare/backend_measurement_report_spec.spl --mode=interpreter --clean`
- `SIMPLE_LIB=src src/compiler_rust/target/debug/simple test test/system/wm_compare/backend_measurement_capture_spec.spl --mode=interpreter --clean`
- `SIMPLE_LIB=src src/compiler_rust/target/debug/simple test test/unit/lib/gpu/engine2d/backend_probe_strict_spec.spl --mode=interpreter --clean`
- `find doc/06_spec -name '*_spec.spl' | wc -l`
