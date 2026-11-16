# Cranelift AOT refuses bare-metal `<arch>-unknown-none` (aarch64 Limine kernel)

- **Status:** verification-pending
- **Severity:** P1 (blocks `build/os/aarch64_limine/kernel.elf` on phase 2)
- **Found:** 2026-11-15

## Symptom
`scripts/os/build-simpleos-aarch64-limine-kernel.shs` with the phase-2 builder
(`~/xc/simple-p2`): every module fails with
`Compile error in backend (cranelift): Failed to create Cranelift AOT module`
(ICE receipt `build/ice/108490_n8314700061889615784/ice_receipt.tsv`). The
retained diagnostic dir holds only that message.

## Root cause
`BuiltinBackendCompileAdapter.cranelift_target_triple`
(`src/compiler/70.backend/backend_plugin/builtin_adapter.spl:38`) feeds the
bare-metal LLVM triple through `backend_normalize_requested_aot_target`
(`src/compiler/70.backend/backend/aot_target_normalization.spl:21`). The
bare-metal triple is `aarch64-unknown-none`, with no env
(`llvm_target.spl:218-228`, built by `to_text` at `:364`). target-lexicon parses
that with `BinaryFormat::Unknown`, and `ObjectBuilder::new` rejects it.
`rt_cranelift_new_aot_module_impl` (`cranelift_sffi.rs:2190`) then returns 0, so
`cranelift_codegen_adapter.spl:310` reports the error. The cause has nothing to
do with memory. `x86_64-unknown-none-elf` fails the same way, and a host target
links.

Minimal repro: a two-function file run with
`simple-p2 native-build --backend cranelift --entry-closure --target aarch64-unknown-none-elf`
fails. The same file run with `--target x86_64-unknown-linux-gnu` links.

## Fix
`backend_normalize_requested_aot_target` maps the env-less 3-part
`<arch>-unknown-none` triple to `<arch>-unknown-none-elf`.
Spec: `test/01_unit/compiler/backend/simpleos_cranelift_target_normalization_spec.spl`.

## Verification pending
The phase-2 builder must be rebuilt, and the Limine kernel built with it.
