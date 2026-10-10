# Bootstrap source projection omits a transitive compiler ABI header

Status: REPAIRED_PROJECTION_PREPARED_FULL_BUILD_PENDING. Bug DB reconciliation is pending; no qualified
pure-Simple database tool is available in this session.

## Actual failure

The final cached seed repair attempt used immutable logical Git tree
`4dc8a469a0257419d753fee475c4033887df48d3`, projected into
`build/minimal-native-producer-20261011/source`. Its 11,612 files included Rust
and runtime owners, but omitted a quoted C include outside those selected roots:

`src/runtime/runtime_backend_plugin.c` includes
`../compiler/70.backend/backend_plugin/abi/simple_backend_plugin_v1.h`.

Cargo exited 101 at this missing header. The actual receipt reports 249 fresh
artifacts and 29 rebuilt artifacts; resource enforcement, source/tool pins,
Windows Job closure and unchanged original cache were valid. There is no new
final compiler executable or native Hello acceptance.

Receipt: `build/minimal-native-producer-20261011/RESULT.json`.
Build request SHA256:
`cde5780ab89c123fabf730c95377e66494d7c7d06cb8600ffdb5c125b371353d`.
The full seed repair ledger has consumed three of three attempts. A further
full build is held pending the user's explicit extension of that limit.

## Reproduction and narrowed passing control

The original frozen projection and failing compiler log remain intact. A
separate object-only control materialized the exact failing C translation unit
and all eight recursively quoted headers from the same Git tree. The real
`clang-cl` invocation with the original compile flags then passed once.

Receipt: `build/backend-plugin-component-20261011/RESULT.json`.
Request SHA256:
`15cc985549b9f0414eadbe8958e8e61caa66305fb267ad74abd960a77e217ee7`.
This proves only that translation unit's compile with its complete header
closure. It does not qualify the full compiler, linking or runtime behavior,
and does not reopen the closed seed ledger.

## Required repair and similar-failure prevention

Extend the actual source materializer to follow quoted C includes recursively
from selected translation units and headers, resolving each relative to its
including file and the declared include roots. Read only the frozen Git source;
reject missing, ambiguous or escaping inputs rather than falling back to live
working files. Include compiler ABI headers even when they lie outside the
initial Rust/runtime source roots. Preserve generated OUT_DIR inputs as a
separate explicit generated-source contract.

Add actual materializer tests for this missing header, recursive relative
headers, multiple include roots, include cycles, missing descendants and
immutable source identity. Enumerate unresolved includes before compilation;
avoid discovering one omitted header per full rebuild. Preserve existing
cache artifacts and reuse only compatible inputs after the projection repair.

No header contents, compiler semantics, stub fallback or unresolved-symbol
policy are changed by the passing component control. Record the eventual
materializer fix commit and verified full build before resolving this report.

## Private materializer repair evidence

The successor uses the same immutable logical tree and reads quoted includes
recursively before creating the physical projection. Eleven distinct host
controls passed across three bounded repair cycles, with no passing controls
replayed. They cover the real omitted-header refusal, eight-header closure,
compact `#include"file.h"`, recursive dependencies, cycles, missing/escaping
inputs and rejection of a changed build-recipe owner.

A source-only preflight identifies 29 translation units selected by the exact
Windows default-feature runtime and terminal build owners, 50 closure files
and 37 quoted edges. It captures both the compiler backend-plugin ABI header
and `tools/counterpart/sdk/c/simple_counterpart_abi.h`. The other 358 includes
are reported as angle/system inputs; none are macro includes. Unrelated browser
and optional LLVM sources are excluded by the recipe, not silently ignored as
missing dependencies. Build-owner changes require a new recipe review.

Evidence is retained under
`build/native_probe/phase3-enum-nil-arm-fix-20261010/tldr-local-file-validity/consumer-bridge/warm-candidate/minimal-product-producer-source-cut4/`.
Root then executed the three pinned implementation files from a separate
receipt directory, preserving the sealed packet. Source preparation completed:
11,614 files and 101,826,390 bytes under
`build/minimal-native-producer-successor-20261011/source`.
Physical-source manifest SHA256:
`5425587a47e37e512e8546210a53846020bf80304579d4a9be5012f605d63b02`.
Receipt directory:
`build/native_probe/phase3-enum-nil-arm-fix-20261010/tldr-local-file-validity/consumer-bridge/warm-candidate/minimal-product-source-preparation-20261011/`.

This is helper and actual source-preparation evidence, not successful compiler
admission. The rebuilt runtime/compiler, native Hello and publication remain
unverified. The original failed source/cache stays intact; the full seed ledger
remains closed at three attempts. Rust/generated-include limitations and
external vendor/SDK inputs still require their existing build-recipe review.
