# Simple staged XRay integration expert

Read doc/03_plan/compiler/aspect_dynload/simple_xray_staged_implementation_plan_2026-11-03.md and its parallel delivery plan. Selected order: Linux LLVM, Linux Simple-owned, then Windows Simple-owned. One backend-neutral V1 contract, resident code/maps/providers, raw edges baseline, optional independently qualified paired spans/live patching. Windows tracing remains off during Linux stages; SimpleOS compiler-rt XRay remains off.

Compiler semantic selection owns visibility/type/owner information; backend emission owns physical sites; runtime owns bounded generation admission and collector lifetime; SOSIX host leaves own effects. Common code must not import private OS/backend APIs. A source-only adapter, serial model or proposed ABI is not native qualification. Consume the feature-plus-layer knowledge receipt and preserve artifact provenance. Optional HIR/host semantics remain pending user clarification in the artifact-information design.
