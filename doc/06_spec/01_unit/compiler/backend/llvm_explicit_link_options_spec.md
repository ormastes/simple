# Explicit LLVM link options

Authored manual, 2026-10-03. Three unexecuted scenarios in
`test/01_unit/compiler/backend/llvm_explicit_link_options_spec.spl` exercise
production option projection and hashing functions.

| Case | Assertion |
|---|---|
| BuildConfig projection | Ordered libraries, search paths and linker flags reach CompileOptions; LLVM backend stays llvm-lib. |
| Final-link projection | Requested libraries/paths survive; explicit flags follow existing flags; existing fallback policy is retained. |
| Cache identity | Changes in every link-input family affect identity; reordered flags and concatenated values cannot share the original identity. |

Production `build_native_llvm` now uses the tested projection rather than the
five-argument convenience API that discarded dependencies. All four ordinary
driver LLVM/hosted output callsites carry those declarations. The orchestrator
passes them into the existing NativeLinkConfig admission/link owner. Strict
rejection of ambient SIMPLE_LINK_OBJECTS remains unchanged; explicit argument
validation and sealed-provider shadow checks still run downstream.

This preserves existing requested-dependency configuration, not a new provider
trust receipt. Options identity records ordered declarations, not current
library bytes. The inspected final-link path executes linking each invocation;
object reuse does not certify an unchanged external provider. LLVM DLL content,
loader search and process-lifetime pinning need separate owner evidence before
ORC use. No LLVM provider was linked or invoked here.
