# Native callback argument becomes null in source-root fallback

Status: OPEN language/compiler defect; production source-closure call site repaired on the Item 5/6 work branch.

At branch revision `e286f79119fa79365a1ed2b5f8b10e2bb8eb8c9a`, the preserved rejected pure-Simple Stage 2 binary crashed when the native-build worker resolved `stage2_module_path_naming.spl`. The crash core is `/var/crash/_tmp_simple-release-targets-worktree-20261010_.simple_storage_build_bootstrap_stage2_aarch64-unknown-linux-gnu_simple.rejected.1000.crash`.

GDB shows PC 0, called from `compiler.common.source_root_resolution.source_root_resolution_with_fallback_v1`. The AArch64 instruction at offset +208 is `blr x7`, and `x7=0` in the core. The source helper's only indirect call is `fallback(module_path, entry_dir)`; the production caller passed `_driver_resolve_entry_import`. This is direct evidence of a null function value in native code, not an HIR shard scheduling failure. A direct replay with `SIMPLE_HIR_SHARDING=0` also crashed in the native-build worker during source closure.

The Item 5/6 branch change `f25b700f050` invokes the existing fallback resolver directly at the driver call site, preserving `Found`, `Missing`, and `Ambiguous` outcomes. A rebuilt pure-Simple Stage 2 candidate (SHA-256 `5f03d7ca69b935133656c07a0eb0154b8095a73609d25669005e2c62e5d09032`) passed its module-path-naming sanity and received Stage 2 parent sanity/provenance receipts. The generic helper and `test/fixtures/compiler/source_root_resolution_probe.spl` still exercise first-class callback arguments and need a separate compiler lowering fix. That fixture also has the unrelated enum payload defect recorded in `source_root_resolution_native_enum_failure_2026-10-11.md`.

Acceptance: a native build of a minimal callback fixture passes the function value through a parameter, invokes it for a Missing result, preserves payloads for Found/Ambiguous, and exits zero under both LLVM and Cranelift. The production Stage 2 naming sanity must stay green.
