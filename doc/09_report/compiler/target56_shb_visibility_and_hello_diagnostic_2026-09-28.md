# Target 5/6 SHB visibility and hello closure diagnostic (2026-09-28)

**Status: focused progress; neither target qualified.**

## Interface metadata and kernel closure

`shb_extractor.spl` imported the nonexistent `compiler.visibility` path and
hardcoded every parsed declaration's public bit to `false`, despite importing
`decl_get_is_pub`. It now imports `compiler.common.visibility` and reads the
actual AST public bit for declarations and the trait extraction helper. A
no-stub Stage2 entry-closure native build of
`test/01_unit/compiler/shb/shb_extractor_visibility_real_spec.spl` compiled
111 units and ran 1/1 examples. The spec parses a real public and private
function, then verifies the SHB interface contains only the public one.
Source, spec, and native binary SHA-256 values are respectively
`c85bbb85e46b1599306d3e6f51515efc3abe018049855fa08e8ef705f122eece`,
`792e9dd7b480ffcd421a5dbcaaf570525267aa6b84e166cb4aa30f2ad067320a`,
and `54b791dfe37441f979f2932c53bd0c2f6601a1bbcbbcc126935f15731a194f24`.

The old `src/compiler/10.frontend/core/compiler/test_mir_codegen.spl` was a
top-level test file in the production source tree, imported the nonexistent
`compiler.core.compiler.mir_codegen`, and had no live source/test/script
references. Removing it and fixing the SHB import reduced the fail-closed
kernel closure check from 2 to 0 unresolved imports. The checker still fails:
2,085 classified files, 3 K0-to-P, 14 K1-to-P, and 10 kernel-to-app/OS
edges. This does not establish a demand-loaded kernel.

## Focused Linux aarch64 hello

The admitted pure-Simple Stage2 compiler SHA-256
`d57b8ff1c676c0e250f76f713a5e8e5b0bbf3d91fd72741698e8fe0f26ad033c`
built `test/05_perf/startup/hello_fixture.spl` using no-stub
`native-build --source src/compiler --source src/app --source src/lib
--entry-closure --entry test/05_perf/startup/hello_fixture.spl --strip`.
The binary printed `hello`, measured 21,016 bytes, and has SHA-256
`16b42a45086093eae6b4ad0d8aaf2ceade790d9256efda8afea18fed8dd4eb3e`.
Build wall and peak RSS were 1.36 seconds and 137,724 KiB. Its only dynamic
dependency is `libc.so.6`; `readelf` reported 207 dynamic symbol entries.

A traced Stage2 link selected a generated core-C runtime archive twice,
`--gc-sections`, and `--as-needed`. It also forced
`prof_sample_force_link`, which retains the profiler constructor in the
unstripped hello. That force root is in the bootstrap native-build path; this
probe does not attribute the full 5,656-byte gap above the 15-KiB Linux
release-small limit. It is pre-Stage4, uses no matched C/Python comparison,
and has no 30-sample startup/RSS cohort, so it cannot pass Phase 5.

## Corrected implementation state

The Phase 3 plan names
`src/compiler/70.backend/linker/runtime_feature_closure.spl` and
`RuntimeFeatureClosureV1` as implemented, but neither exists on this branch.
The current pure-Simple linker has retained-symbol and runtime-bundle
selection; it lacks the exact closure manifest and associated admission
receipt claimed by that dated plan. Implement that source-to-link contract,
remove the remaining forbidden kernel edges without dropping VHDL/C/GPU
features, and obtain Stage4 plus matched size/startup evidence before
qualifying Target 5. Target 6 still requires the typed graph publisher and
full entrypoint cutover.
