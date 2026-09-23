# LLVM 23.1 provider verification and remaining guest checks

Scope: PR #1263, implementation commit `193bfd8a80c`.

The provider admission and receipt fixes have scoped Astra review approval.
Preserving the `clang++` and `ld.lld` invocation names selects the appropriate
driver while canonical paths and binary hashes still constrain the provider.
The changes add no guest allocation or persistent runtime state.

Existing evidence is retained under `build/evidence/llvm23-provider/`:

| Check | Evidence | Result |
| --- | --- | --- |
| FreeBSD provider contract | `freebsd-provider-contract-final.time` | exit 0; 0.13 s; 2,068 KiB peak RSS |
| QMP provider/dispatcher regression | `qmp-provider-self-test.time` | exit 0; 0.05 s; 3,580 KiB peak RSS |
| SimpleOS toolchain and wchar ABI | `simpleos-sysroot-toolchain-final.time` | exit 0; 0.11 s; 47,792 KiB peak RSS |
| Installed LLVM 23.1 provider admission | `installed-provider.time` | exit 0; 2.80 s; 31,176 KiB peak RSS |

These passing checks were not repeated for the documentation update. They do
not establish end-to-end bootstrap, target correctness, or guest performance.

## Outstanding verification TODOs

- TODO (FreeBSD owner): after Linux bootstrap succeeds, run
  `/usr/bin/time -v -o build/freebsd-qemu-full.time env QEMU_CPUS=12 QEMU_BUILD_JOBS=12 sh scripts/check/check-freebsd-bootstrap-qemu.shs --full`
  from the integrated PR revision. Use the pinned FreeBSD 14.4 cloud image,
  admitted LLVM 23.1 provider, SSH key, adequate overlay space and memory.
  Capture the provider receipt, elapsed time, and maximum resident set size
  from `build/freebsd-qemu-full.time`. The existing guest began from an older
  source snapshot and cannot validate this change. Rust seed/Stage 2/3 and its
  `cargo test -p simple-compiler` gate remain under `FREEBSD_RUST_SEED_ENV`
  (LLVM 18) because of the pinned Inkwell binding; LLVM 23 is restricted to
  pure-Simple post-bootstrap gates.
- TODO (SimpleOS sysroot owner): integrate and verify the separately owned
  freestanding runtime/sysroot fixes. The existing full sysroot attempt
  (`sysroot-build-fixed.log`) fails compiling `runtime_native.c`, including
  a missing `glob.h`; this toolchain PR does not claim that build passes.
- TODO (SimpleOS QEMU owner): after Linux bootstrap and sysroot admission,
  use `scripts/check/build-simpleos-arm64-desktop-engine2d-attested.shs`,
  then `scripts/check/check-simpleos-arm64-qmp-input-evidence.shs` with the
  admitted Phase 3 compiler and LLVM 23.1 prefix. Retain guest receipts,
  provider hashes, QMP input/frame evidence, and time/RSS measurements.
- TODO (FreeBSD Phase 2 owner): as soon as the FreeBSD Phase 2 compiler is
  admitted, run the compiler, interpreter, and loader binary tests in the
  same QEMU guest. Wrap each binary invocation with `/usr/bin/time -l`, retain
  its exit status, elapsed time, and `maximum resident set size`, and bind the
  receipts to the Phase 2 binary SHA-256 and integrated source revision.

Overall platform verification remains pending; only the provider contract
and dispatcher/header regression checks above are recorded as passing.
