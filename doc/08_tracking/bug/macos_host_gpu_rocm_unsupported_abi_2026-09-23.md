# macOS host-gpu ROCm unsupported-host ABI

Status: focused macOS verification PASS; independent final review pending. Based on PR #1390, commit
`9414ea422719e1b3b25f84b8d77eba8caa6d0fd1`.

## Defect and correction

After the implementation-method receiver correction, the production RocmFfi
native fixture compiled but failed to link `rt_rocm_init`,
`rt_rocm_is_available`, and `rt_rocm_shutdown`.

The frozen Stage 2 `libsimple_native_all.a` already exports these symbols.
The diagnostic Rust native builder's explicit `host-gpu` lane instead builds
the core-C provider-loader archive from source. Its source list omitted
`runtime_rocm.c`, even though that canonical owner implements the non-Linux
unsupported-HIP ABI: initialization/availability return false and shutdown
returns true without acquiring resources. This is a source-selection defect,
not a missing AMD driver or a reason to manufacture test-only symbol bodies.

The correction includes that existing owner only when building the dynamic
loader composition for a non-Linux target. Linux continues to exclude the real
HIP implementation from this archive. No C implementation, provider ABI,
provider discovery, or production Simple owner is changed. The existing input
fingerprint and exact-member checks include the new source automatically.

## Acceptance and scope

- The existing host-gpu archive regression checks the three lifecycle exports
  on macOS and their absence on Linux.
- `test/fixtures/native/rocm_init_receiver/main.spl` exercises the production
  owner with an absent dynamic provider, preserving its six-case contract.
- `test/fixtures/native/rocm_unsupported_host/main.spl` is explicitly non-Linux:
  it exercises the three canonical static lifecycle responses.
- Diagnostic compiler/native runs use private caches, no generated stub
  fallback, bounded time, and process-tree RSS enforcement.
- Object size and the unsupported lifecycle instructions establish the local
  code-size/operation cost; no full CLI throughput claim is made.

Evidence root:
`/Users/ormastes/simple-tmp/phase2-rocm-init-20260923/build/evidence/rocm-host-gpu/`.

This is not physical ROCm execution or provider admission. Full Phase2 and
source-matched bootstrap admission remain separate gates. Linux source
exclusion is covered by the authored platform test; Linux execution requires a
Linux runner.

## Executed evidence

Diagnostic compiler SHA-256:
`3b0e7d0ead805dbee9f4bb3fba86c00cf4312d31c52f1afa367194bc6b6e9adc`.
The private bootstrap-profile build used pinned Rust/LLVM, one Cargo job,
LTO disabled and 16 codegen units: 250.34 seconds, sampled process-tree peak
3190736 KiB against an enforced 5859375 KiB cap. This compiler is a diagnostic
artifact, not an admitted replacement bootstrap compiler. Existing nonfatal
rust-objcopy LLVM-dylib warnings remain outside this fix.

Both native commands use `SIMPLE_NATIVE_BUILD_RUST=1`,
`SIMPLE_NO_STUB_FALLBACK=1`, the matching frozen Stage 2 host-gpu runtime path,
one native build thread, and independent compiler-SHA/fixture caches. Exact
commands are retained in `run-cargo.shs` and `run-owner.shs` beside the logs.

- `rocm_unsupported_host`: build 6.88 seconds, peak 287488 KiB, native run
  `PASS cases=3 provider=unavailable`.
- `rocm_init_receiver`: build 5.33 seconds, peak 286624 KiB, native run
  `PASS cases=6 provider=absent`.
- Each run sampled 2320 KiB. Build/run limits were 976562 KiB; all receipts
  report zero observer errors, zero exit status, and quiescent cleanup.
- `archive-symbols.log` checks the actual selected host-gpu archive: exactly
  one definition each of init, is_available, shutdown, and provider_loaded.
- The added `runtime_rocm.o` is 2176 bytes on disk, containing 284 bytes text
  and 24 bytes constants. Each lifecycle hook disassembles to a constant move
  plus return: no provider load, allocation, copy, or extra runtime call.

The extended Rust archive test was authored but not separately built/run: the
actual native-selected archive inspection supplied the macOS symbol gate
without another large test build during disk-capacity recovery. Linux CI must
execute the platform-conditional test to establish its runtime exclusion gate.
The direct-env working-tree guard and doc-spec layout check passed; the SFFI
backlog inventory remains source-only evidence, not provider admission.
