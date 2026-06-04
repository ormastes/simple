# Graphical Backend Equality — System Test Plan

Date: 2026-06-03

## Focused Spec

```bash
SIMPLE_LIB=src src/compiler_rust/target/release/simple test test/03_system/wm_compare/graphical_backend_equality_spec.spl --mode=interpreter --clean --format json
```

## Assertions

- Backend selector accepts `2d:cpu` and composed `gui:electron+wm:host`.
- Invalid backend selectors fail closed with reasons.
- Capture metadata validates dimensions, scale factor, capture kind, and pixel
  buffer length.
- Exact CPU/software comparisons require exact match.
- Portable GPU/Web diagnostics can report thresholded matches without hiding
  the policy.
- Backend unavailability remains separate from drawing equality.
