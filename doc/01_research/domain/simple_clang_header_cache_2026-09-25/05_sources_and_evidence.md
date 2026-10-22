# Report 5 — Sources, executed probes, and evidence limits

**Research date:** 2026-09-25  
**Source policy:** Primary project documentation and upstream source. No repository or GitHub settings were modified. This extension is not a fresh source audit of `ormastes/simple`.

## Evidence categories

**Design proposal.** The strict registry, exception semantics, completeness contracts, Simple C ABI/provider, launcher subcommands, and CI gates are proposed by these reports. They are not claimed to exist in an installed Simple release.

**Upstream facts.** The references below establish available Clang/CMake/Ninja mechanisms and documented limitations. Online `latest` and LLVM `main` pages may describe development versions. Use the exact headers/options of the implementation's pinned toolchain; do not infer that Clang 17 has every API appearing in current Doxygen.

**Local execution.** Twelve small native counterexample probes were executed using the tools recorded below. These validate selected language/build-tool behaviors, not the soundness, performance, or completeness of the proposed cache.

**Prior session plan.** The supplied four-report build-platform plan is copied unchanged into [prior_plan](prior_plan/README.md). Its existing repository findings belong to its stated historical audit commit, `ed75897fe050d874ce7c7bcd90c2b30953ad65ce`; they were not re-established against a newer tree in this extension.

## S01

[Clang: Modules](https://clang.llvm.org/docs/Modules.html)

Relevant sections: configuration macros, module variants, textual headers and context options. The document describes `config_macros` and its limited warning behavior, and says the `exhaustive` variant-reduction optimization is not implemented. This is not the proposed project-wide strict allowlist. `-fmodules-ignore-macro` is not a substitute for an approved varying-macro policy.

## S02

[Clang: Precompiled Header and Modules Internals](https://clang.llvm.org/docs/PCHInternals.html)

Establishes native serialization and lazy loading of compiler state. Used to distinguish a native serialized prefix/module resource from a string of preprocessed tokens or a pointer to a live AST. It does not certify arbitrary fragment replay by an external cache.

## S03

[Clang Doxygen: PPCallbacks](https://clang.llvm.org/doxygen/classclang_1_1PPCallbacks.html)

Establishes the available observation family for preprocessing. The retrieved Doxygen describes a development toolchain, not the locally tested compiler. API presence alone does not prove a complete negative macro/file dependency set; additional instrumentation or conservative full-context identity remains necessary.

## S04

[LLVM upstream: clang/tools/clang-shlib/CMakeLists.txt](https://github.com/llvm/llvm-project/blob/main/clang/tools/clang-shlib/CMakeLists.txt)

The inspected upstream file defines a `clang-cpp` shared-library target and its build constraints. The `main` URL is a moving reference; production must pin a commit and verify its platform-specific targets. This report did not build that library.

## S05

[Clang: Choosing the Right Interface for Your Application](https://clang.llvm.org/docs/Tooling.html)

Distinguishes the deliberately stable, limited libclang C surface from the richer C++ tooling interfaces and their evolution. Supports placing an exact-version adapter behind Simple's own controlled C ABI; it does not promise compatibility between arbitrary Clang builds.

## S06

[clangd: Threads and request handling](https://clangd.llvm.org/design/threads)

Documents thread-safe immutable preamble bytes and non-thread-safe live ASTs. This is evidence for the serialized-resource/private-context boundary, not proof that all Clang frontend actions are automatically safe to multiplex.

## S07

[LLVM: Building a Distribution of LLVM](https://llvm.org/docs/BuildingADistribution.html)

Relevant to consolidated versus per-component shared libraries, supported LLVM-dylib packaging, and performance/distribution tradeoffs. The documented LLVM-dylib mechanism excludes Windows; the report's Linux build template must not be treated as a verified Windows recipe. Neither the static nor dynamic provider template was executed here.

## S08

[CMake: `<LANG>_COMPILER_LAUNCHER`](https://cmake.org/cmake/help/latest/prop_tgt/LANG_COMPILER_LAUNCHER.html)

Establishes compiler-launcher integration for supported Makefile/Ninja generation. A launcher wraps an actual compiler invocation; it is not an always-run build-policy hook. P11 demonstrates the distinction locally.

## S09

[CMake: File API](https://cmake.org/cmake/help/latest/manual/cmake-file-api.7.html)

Establishes the versioned codemodel and related target/configuration/compiler metadata. The plan uses it for semantic ownership and configuration mapping, not as a replacement for every native build command or dynamic dependency. Actual invocations/native graph execution remain authoritative until a complete execution adapter exists.

## S10

[CMake: `target_precompile_headers`](https://cmake.org/cmake/help/latest/command/target_precompile_headers.html)

Documents native PCH creation, `REUSE_FROM` matching requirements, and controls to disable PCH use. Supports explicit compatible prefix resources rather than automatically combining unrelated targets' headers.

## S11

[CMake: `OBJECT_DEPENDS`](https://cmake.org/cmake/help/latest/prop_sf/OBJECT_DEPENDS.html)

Documents additional object prerequisites for supported Makefile/Ninja generators, not Visual Studio/Xcode. P12 exercises one practical policy-dependency mechanism. It is a building block, not the whole content-addressed or no-cache execution contract.

## S12

[CMake: `CMAKE_EXPORT_COMPILE_COMMANDS`](https://cmake.org/cmake/help/latest/variable/CMAKE_EXPORT_COMPILE_COMMANDS.html)

[Clang: JSON Compilation Database Format Specification](https://clang.llvm.org/docs/JSONCompilationDatabase.html)

Documents exported translation-unit invocations and their representation. Use the current CMake documentation for generator support. A compilation database is useful for TU discovery but is not a complete build, link, generator or test graph.

## S13

[Clang: Standard C++ Modules](https://clang.llvm.org/docs/StandardCPlusPlusModules.html)

Documents the standard-module compilation/dependency workflow. Supports keeping this provider kind separate from header modules and PCH. Named-module support must be qualified for each pinned Clang/CMake version rather than inferred from generic PCM terminology.

## S14

[GCC preprocessor manual: Standard Predefined Macros](https://gcc.gnu.org/onlinedocs/cpp/Standard-Predefined-Macros.html)

Primary compiler documentation used as a reference for context-sensitive standard builtins such as file, line, date and time. It is not evidence that every GCC-specific extension behaves identically in Clang. Clang-specific counter/state behavior in this report is supported separately by P09.

## S15

[Ninja: Manual](https://ninja-build.org/manual.html)

Documents the native graph/execution model, dependency categories, variable and file scopes, pools, response files, generator behavior and dynamic dependencies. Used to define the completeness obligation for an optional Ninja adapter, rather than suggesting a line-oriented importer is sufficient.

## Executed local environment

| Tool | Actual local version |
|---|---|
| Clang | 17.0.0, Swift LLVM build `10999b6d034fe318f3d56c83bddb6572593a8bb0` |
| Clang target | `x86_64-unknown-linux-gnu` |
| CMake | 3.31.6 |
| Ninja | 1.12.1 |

These are the available test tools, **not a recommendation to pin the implementation to Clang 17**, nor a statement of the newest available versions. No cross-platform or shared-library build qualification was performed.

## Executed probe outcomes

All **12/12** counterexample probe groups passed their explicit expected outcomes. Some PASS results deliberately demonstrate a limitation—for example, P11 passes when the undeclared policy change does not invoke the launcher.

| Probe | Observation |
|---|---|
| P01 | Undefined, zero, empty and one definitions differ. |
| P02 | A previously unexpanded identifier can become a macro dependency. |
| P03 | Ordered `-D/-U` operations change preprocessing. |
| P04 | A newly present optional include changes output despite its prior absence from an ordinary depfile. |
| P05 | Include-search ordering can select different header contents. |
| P06 | One X-macro fragment is intentionally expanded twice under different definitions. |
| P07 | Entering packing state changes layout for the same header on the tested ABI. |
| P08 | A preceding typedef changes the meaning of an otherwise identical header. |
| P09 | `__COUNTER__` depends on entering state. |
| P10 | Native Clang rejects the tested incompatible PCH macro configuration. |
| P11 | CMake launcher/File API integration works; an undeclared policy-only edit is skipped by Ninja. |
| P12 | Adding the policy file as an object prerequisite triggers compilation in that case. |

Full observed outcomes are in [probe_results.md](evidence/probe_results.md), commands/outputs in [probe_results.json](evidence/probe_results.json), and all fixture construction in [run_probes.py](evidence/run_probes.py). The script creates a temporary work directory and removes compiled outputs after the run. It can be rerun with Python 3 and the required native tools on PATH; fixed layout assertions are specific to the tested x86_64 ABI.

The 56 HC acceptance scenarios in Report 4 are **not** counted as executed. They require a future implementation. The bundled SDN is an authoring example, not parser-validated configuration. The policy text in P11/P12 was intentionally opaque to the logging launcher; those probes do not implement macro enforcement.

## What remains unproven

No measured throughput improvement, sub-minute CI performance, end-to-end cache soundness, Clang C++ ABI compatibility, compiler-group reentrancy, complete preprocessor replay, SDN parser compatibility, distributed failure recovery, or repository integration is claimed. The design explicitly retains conservative/isolated reference paths until those properties are qualified.
