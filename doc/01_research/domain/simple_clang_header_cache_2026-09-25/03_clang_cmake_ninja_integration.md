# Report 3 — Clang library provider and CMake/Ninja integration

**Date:** 2026-09-25  
**Status:** Proposed integration plan. The native-tool probes in `evidence/` are executed examples; the Simple launcher/provider commands below are not implemented by this report.

## 1. Corrections and final decisions

| Earlier simplification | Final integration rule |
|---|---|
| A Clang dynamic library is inherently faster. | Persistent lifetime and resource reuse are the main benefits. Compare dynamic and static provider builds under the same lifetime. |
| CMake File API supplies the complete executable build DAG. | Use it for target/configuration metadata; retain Ninja for exact native execution until an execution adapter is complete. |
| A compilation database is enough to rebuild a project. | It describes compile invocations, not all generator, link, install, test, and dynamic-dependency actions. |
| A compiler launcher enforces every build request. | It runs only when the underlying builder invokes a compilation; policy-only/no-cache work needs explicit top-level validation and invalidation. |
| A list of varying macros is sufficient for every header AST. | Header context can include previous semantic declarations; use native serialization boundaries or textual processing. |
| A vendor exception can ignore a macro in the key. | The exception must retain complete context or disable semantic reuse. |

Use **CMake + Ninja + Simple compiler launcher + SDN policy + optional File API metadata** as the first production integration. This requires no new CMake generator and no initial Ninja reimplementation.

## 2. Clang as a library: what exists

Upstream defines a `clang-cpp` shared-library target assembled from Clang components; its build requires the relevant PIC support and has platform-specific linking details. This establishes an available integration substrate, not a complete Simple provider. [S04](05_sources_and_evidence.md#s04)

`libclang` supplies a deliberately limited stable high-level C interface. Full frontend/preprocessor control needs the C++ implementation interfaces or a tailored adapter, whose API evolution must be managed. [S05](05_sources_and_evidence.md#s05)

Recommended boundary:

```text
Simple group/mid-scheduler
    -> stable, versioned Simple C ABI
        -> pinned C++ adapter
            -> clang-cpp OR statically linked Clang components
                -> private compiler/frontend contexts per request
```

The wrapper exports lifecycle, invocation creation, policy observation, dependency capture, native resource production/consumption, compilation, cancellation, and result collection. No `std::string`, `ASTContext*`, C++ exception, or allocator ownership crosses the external ABI. Use explicit byte spans, opaque scoped handles, status codes, and release functions.

Pin the adapter, Clang/LLVM libraries, runtime, resource directory, and serialization schema together by digest. “Clang major version matches” is not sufficient binary compatibility. Separate incompatible versions into different group processes; do not load several conflicting LLVM copies into the trusted scheduler.

## 3. Dynamic versus static provider packaging

A shared `clang-cpp` provider is convenient for initial implementation and independent toolchain distribution. A static-component provider may provide better optimization or deployment characteristics. Both can be persistent and both can use shared binary resources.

LLVM distribution guidance warns against using `BUILD_SHARED_LIBS=ON` to make every component a shared library. It recommends its consolidated LLVM-dylib mechanism where supported; that mechanism is documented as unavailable on Windows. Therefore a Linux recipe cannot be presented as a universal Windows DLL recipe. [S07](05_sources_and_evidence.md#s07)

A **non-executed, Linux-oriented build template** for a pinned source tree is:

```sh
cmake -S /src/pinned-llvm-project/llvm -B /build/clang-provider -G Ninja \
  -DCMAKE_BUILD_TYPE=Release \
  -DLLVM_ENABLE_PROJECTS=clang \
  -DLLVM_ENABLE_PIC=ON \
  -DBUILD_SHARED_LIBS=OFF \
  -DLLVM_BUILD_LLVM_DYLIB=ON \
  -DLLVM_LINK_LLVM_DYLIB=ON \
  -DCLANG_LINK_CLANG_DYLIB=ON
cmake --build /build/clang-provider --target clang-cpp clang clang-scan-deps
```

Resolve options and exported targets against the selected LLVM revision. For Windows, qualify the available `clang-cpp`/runtime packaging or use a private provider DLL/executable statically linked to the necessary components behind the same Simple C ABI. This report does not build or test either shared-library package.

Benchmark fresh CLI, warm singleplex, dynamic-library group, and static-library group. Do not credit OS-shared executable pages as an advantage unique to dynamic linking; do not claim a numeric speedup without measurements.

## 4. Header-policy enforcement adapter

The adapter must receive the real resolved driver invocation, not a reconstructed command containing only include directories and definitions. Preserve compiler selection, target, response files, `-D/-U` ordering, forced includes, CWD interpretation, environment, resource paths, diagnostic modes, and all produced side files.

Install provider observations before preprocessing. At each supported resource boundary, evaluate the policy and build/validate its context witness. On a PCH/module hit, validate the resource's stored policy/observation evidence; callbacks for an already materialized resource may not repeat every original event.

A frontend plugin can be an incremental way to emit project diagnostics and manifests, but **does not automatically provide complete failed-lookup or arbitrary replay instrumentation**. Maintain a capability matrix per pinned provider. Unsupported precision stays full-context, isolated, or no-cache rather than claiming completeness.

The early useful mode is an external Clang process with policy validation and explicit PCH/module actions. The later in-process mode uses the same action/resource contract. A preprocessor-only pass is not sufficient to execute code generation; the C++ wrapper must create the appropriate compilation action and return all expected outputs.

## 5. Native resource boundaries

Use `target_precompile_headers()` for suitable CMake-managed prefixes. CMake documents that `REUSE_FROM` requires matching compiler options, flags, and definitions; unrelated targets must not share a PCH just because their header list matches. It also provides target/source controls for disabling PCH use. [S10](05_sources_and_evidence.md#s10)

For Clang header modules, admit a reviewed module map and isolated module build environment. For standard C++ modules, keep their explicit dependency graph and native provider kind; do not equate them with header modules or a general `#include` result. [S13](05_sources_and_evidence.md#s13)

Do not transform arbitrary textual includes into imports merely to gain speed. A non-modular header may rely on caller macros, repeated inclusion, or surrounding declarations. Register it as a textual/complex boundary or leave it uncached. Use the strict policy to identify such boundaries, not to silently alter source semantics.

## 6. CMake launcher path: first implementation

CMake's `<LANG>_COMPILER_LAUNCHER` property supports launcher commands with Makefile/Ninja generators. The launcher is passed the compiler and its arguments, enabling the external tool to delegate or distribute compilation. [S08](05_sources_and_evidence.md#s08)

Illustrative setup once `simple cc-launch` exists:

```sh
cmake -S . -B build/simple -G Ninja \
  -DCMAKE_C_COMPILER=/toolchains/pinned/bin/clang \
  -DCMAKE_CXX_COMPILER=/toolchains/pinned/bin/clang++ \
  -DCMAKE_EXPORT_COMPILE_COMMANDS=ON \
  '-DCMAKE_C_COMPILER_LAUNCHER=/tools/simple;cc-launch;--policy;/project/config/header_policy.sdn;--' \
  '-DCMAKE_CXX_COMPILER_LAUNCHER=/tools/simple;cc-launch;--policy;/project/config/header_policy.sdn;--'
cmake --build build/simple
```

The last command alone gives launcher interception for native dirty compiles. The complete Simple policy requires the top-level preflight/driver described next. Paths are examples, and the Simple subcommand is proposed.

The launcher must preserve the compiler contract: correct exit status, per-action diagnostics, `.o/.obj`, dependency outputs, split debug files, module outputs, and platform-specific auxiliary outputs. Capture all declared results atomically. Treat unknown side effects as unsupported rather than returning a fake object-cache success.

It must not recursively relaunch itself. Record an invocation identity; unwrap only explicitly recognized launchers. Nesting Simple with ccache/sccache is disabled by default because an outer or inner cache can bypass policy/observation. A qualified stacked mode needs a precise ordering and complete evidence contract.

## 7. Crucial gap: Ninja may never call the launcher

The local integration probe configured a real CMake/Ninja project, ran it through a logging compiler launcher, then changed an undeclared policy file. Ninja considered the object up to date and **did not invoke the launcher**. Adding the file as an object dependency caused recompilation. [P11/P12 evidence](evidence/probe_results.md)

Therefore provide two controls:

**Top-level policy gate.** Every requested Simple build validates the current effective policy/profile and examines which previously accepted actions are still eligible. A native Ninja no-op is not sufficient admission evidence.

**Native invalidation bridge.** Add policy/profile/effective-input stamps as dependencies of governed native objects. In supported CMake Makefile/Ninja projects, `OBJECT_DEPENDS` can declare additional object prerequisites; it is not implemented by the Visual Studio/Xcode generators. [S11](05_sources_and_evidence.md#s11)

Minimal native example:

```cmake
# Real CMake syntax. The complete Simple helper is still proposed.
set_property(SOURCE main.cpp APPEND PROPERTY OBJECT_DEPENDS
  "${CMAKE_SOURCE_DIR}/config/header_policy.sdn")
```

For scalability, generate stable per-target/effective-policy stamps instead of rebuilding the repository after any unrelated exception edit. Write a stamp only after validating its inputs. When its content changes, the adapter must ensure native invalidation observes it; do not assume coarse timestamps or a preserved mtime prove content equality.

For a `none` resource, force the selected enclosing semantic action to run on each explicit build request, for example through a governed per-invocation dependency stamp. Merely declining a Simple cache hit is insufficient if Ninja already skipped the action. If the adapter cannot enforce the required dirty state, reject that cache policy in delegated mode or execute the selected action through the full Simple executor.

A direct bare `ninja` invocation without integration may be useful for development, but must not be advertised as producing the complete Simple policy receipt. CI uses the gate-enabled entry point. Do not force rebuilds by touching source files or silently weakening the registry.

## 8. File API and compilation database roles

Use CMake File API to label targets, configurations, source groups, compile settings, dependencies, toolchains and CMake-origin diagnostics. Its codemodel supplies optional compiler command fragments and related metadata; this is not an authoritative replay of every build action. [S09](05_sources_and_evidence.md#s09)

Use `compile_commands.json` for TU discovery and developer tooling. CMake supports exporting it for Makefile/Ninja generators; its presence does not establish all prerequisites or link/custom-command behavior. [S12](05_sources_and_evidence.md#s12)

Translate imported metadata to the Simple typed/SDN model. Keep JSON at the CMake boundary; the native protocol remains SDN. Record the File API object versions and reject unsupported required fields rather than assuming all installed CMake versions expose current online documentation.

At execution, the launcher-observed ordered invocation is authoritative for that compile. If its flags differ from the imported expectation, update/revalidate the graph or reject; never execute with a stale reconstructed command. Configuration-specific definitions are registered profiles, not an excuse to accept arbitrary per-file flag drift.

Do not try to evaluate `CMakeLists.txt`, generator expressions, `find_package()`, or platform probes in Simple. Let CMake configure. A cached configure result requires the complete probe/environment/package/tool closure and relocatability contract; hashing only `.cmake` source files is insufficient. Initially retain CMake's own reconfigure mechanism inside the tracked build adapter.

## 9. Generated files, configure probes and source snapshots

Generated configuration headers are producer outputs with explicit graph edges. The compiler cannot infer a current generated header from yesterday's file at the same path. The native bridge must order producer completion before scanning/compilation.

Configure-time compiler probes use an explicit `configure-probe` profile; they are not automatically authorized as final product artifacts. Scope any broader flexibility to that profile and do not let it publish product object-cache entries. Preserve the exact probe flags and toolchain even when no product target exists yet.

The Simple driver snapshots all declared inputs or validates them against a complete immutable view. Native Ninja is still timestamp-oriented; a same-mtime content change must be detected by Simple's digest-based planning and reflected into native dirty state. Delegation without this bridge is a compatibility mode, not a claim of authoritative content-based CI.

## 10. Ninja import: later full execution adapter

Keep a separate `NinjaAdapter` for projects generated by CMake, Meson, GN, or other tools. It is an execution-format adapter, not a replacement for configuration semantics.

Before claiming complete support, implement and test:

| Feature group | Required semantics |
|---|---|
| Parsing | Escaping, continuations, variable expansion, scope, `include` and `subninja`. |
| Graph | Explicit/implicit/order-only/validation dependencies, multiple outputs, phony/default targets. |
| Runtime dependencies | depfiles, supported `deps` behavior, dynamic `dyndep` updates and generated inputs. |
| Execution | Native shell/Windows command rules, response files, pools, console ownership, cancellation. |
| Incrementality | Command identity, `restat`, generator regeneration, missing outputs, build-file rebuild/reload. |
| Provider capture | Exact known compile actions and side files; no guessed arguments from command-string splitting. |

Ninja explicitly supports dynamically discovered inputs/outputs and updates its graph from dyndep files. Ignoring them can break first-build ordering. [S15](05_sources_and_evidence.md#s15)

On unsupported constructs, delegate the **complete necessary native graph boundary** or return unsupported. Do not execute an apparently safe subset while dropping its dependencies. Only one engine schedules a given graph boundary: Ninja may schedule native actions while the launcher handles each compile's internal resources; a future full Simple adapter replaces that role rather than racing it.

## 11. Final integration sequence

1. Implement the strict SDN registry and complete invocation capture against isolated Clang.
2. Add a CMake compiler launcher and an always-run policy gate with native dependency stamps.
3. Add explicit compatible PCH/module resource actions and the shared resource service.
4. Import File API metadata for ownership, profile mapping and diagnostics; keep native execution.
5. Qualify pinned C++/C-ABI library providers and grouped compilation against isolated behavior.
6. Implement complete Ninja execution support only where its maintenance cost is justified.

This sequence delivers useful header/resource reuse and distributed compiles without first implementing CMake or Ninja from scratch.
