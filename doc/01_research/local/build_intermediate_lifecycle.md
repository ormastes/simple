<!-- codex-research -->
# Build Intermediate Lifecycle — Local Research

Simple already separates durable native cache objects from private publish staging files. Incremental objects under the native cache are reusable evidence and must not be deleted after successful builds. The CLI creates sibling files named `<output>.simple-native-build-<pid>-<micros>.tmp`, but previously checked only the newly generated unique name, so crash leftovers were never reclaimed. The bootstrap LLVM route separately creates temporary `.o` and `.ll` files and now removes them after copying unless `SIMPLE_KEEP_LLVM_IR=1`.

The safe implementation boundary is therefore:

- retain cache objects, receipts, manifests, final output, and requested SMF/object/archive/shared outputs;
- remove private staging output after failure by default;
- remove bootstrap `.o`/`.ll` after successful publication by default;
- reclaim only managed staging siblings older than 24 hours at build start, avoiding live concurrent builds;
- expose one product-wide keep switch and one print switch while retaining the legacy LLVM-specific switch.

Primary owners are `src/app/io/_CliCompile/compile_targets.spl`, `src/app/io/_CliCompile/build_intermediate_policy.spl`, and `src/compiler/80.driver/driver_bootstrap.spl`.
