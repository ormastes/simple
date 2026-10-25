# P4-RAWSTR: native-build surface skeleton cuts functions at column-0 triple-string content

Date: 2026-10-25. Class: P4-RAWSTR. Status: fixed in source; workaround tagged `WA-P4-RAWSTR`.

## Symptom
Phase-4 full-CLI `native-build` (stage2) failed at the parse phase:
- `backend_intel_kernels.spl: 134:14: expected ), got Ident 'uint'`
- `backend_metal_msl.spl: 46:1: ... 'use # for comments'`

## Root cause
Not the lexer: `10.frontend/core/lexer_struct.spl` lexes `r"""` correctly
(single-line `r"""..."""` native-builds fine). The failing path is
`driver_surface_parse_text_v1` -> `module_surface_skeleton_v1`
(`src/compiler/80.driver/cache/module_surface_skeleton_v1.spl`), which stubs
function bodies by indentation: a body ends at the first line indented <= the
header. It had no triple-string awareness, so a body whose `"""`/`r"""` string
carries column-0 content (GPU kernel source) was cut at the first content line,
and the remaining string content was emitted verbatim and parsed as code.
Reproduced with a plain `"""` too; not raw-specific.

## Fix
`_skel_string_continuations_v1` marks lines that start inside a triple string;
those lines stay in the current body (and in trait blocks) and are never treated
as declarations.

## Workaround (until a compiler carrying the fix is deployed)
Each function in `src/lib/gc_async_mut/gpu/engine2d/backend_{intel_kernels,metal_msl,rocm_kernels,vulkan_glsl}.spl`
that returns a multi-line raw string is marked `@inline` (tagged `# WA-P4-RAWSTR`):
the skeleton keeps `@inline` bodies verbatim, so the whole file passes through
unchanged. String contents are byte-identical. Remove the `@inline` + tag once
the deployed stage2 includes the skeleton fix.

## Verification
stage2 native-build of a repro (`@inline fn` + column-0 `r"""` body, importing
copies of the intel/metal files): parse phase passes (no parse errors). Without
`@inline` the same repro fails `3:20: expected ), got Ident 'x'`.
