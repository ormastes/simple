# Portable Compute Toolchain Evidence

Date: 2026-07-19

| Target | Kind | Status | Reason | Bytes | Artifact |
|---|---|---|---|---:|---|
| cuda | optimization | compiled_artifact_verified | pass | 5839 | build/portable_compute_toolchains/simple_2d_optimization.ptx |
| cuda | font-atlas | candidate_compiled | pinned-artifact-identity-mismatch | 4846 | build/portable_compute_toolchains/simple_2d_optimization_font_atlas.ptx |

## Commands

- cuda source emitter: `/tmp/simple-font-publish-20260717/build/portable_compute_toolchains/portable-compute-emitter cuda`
- cuda optimization: `nvcc --ptx -arch=compute_75 -o build/portable_compute_toolchains/simple_2d_optimization.ptx build/portable_compute_toolchains/simple_2d_optimization.cu`
- cuda font-atlas: `nvcc --ptx -arch=compute_75 -o build/portable_compute_toolchains/simple_2d_optimization_font_atlas.ptx build/portable_compute_toolchains/simple_2d_optimization_font_atlas.cu`
