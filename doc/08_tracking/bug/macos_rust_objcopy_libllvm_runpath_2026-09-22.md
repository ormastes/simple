# macOS Rust executable stripping cannot locate its bundled LLVM library

Status: fixed in bootstrap authority routing; full bootstrap pending.

The Stage 2 preparation log at
`build/evidence/macos-enforced-bd544/stage2-reviewed-531ac33/rust-compiler-backfill-build.log`
records `rust-objcopy` PID 7959 aborting while stripping the
`simple-compiler-backfill` build-script executable. Cargo reports a warning and
continues, so Cargo exit status alone does not establish that stripping worked.

The installed `nightly-aarch64-apple-darwin` toolchain selects Rust
`1.100.0-nightly (215a8af4b 2026-09-15)`, LLVM `23.1.1`. Its helper lives at
`lib/rustlib/aarch64-apple-darwin/bin/rust-objcopy` and depends on
`@rpath/libLLVM.dylib`; its loader-relative runpath searches the adjacent
`../lib`, while the actual library is at the toolchain's top-level
`lib/libLLVM.dylib`. The bootstrap's `env -i` correctly excludes ambient loader
configuration, exposing this distribution layout mismatch.

The authority resolver now includes canonical helper/library paths, their
SHA-256 identities, and Rust's LLVM version in the existing seed and tool
snapshots. The helper's actual Mach-O dependencies select an explicit
`private-dylib` or `absent` library mode, which is included in those snapshots.
Statically linked helpers need no external LLVM library and reject stray
capsules and DYLD assignments. Before Cargo runs in dynamic mode, bootstrap
streams the selected library into a
private, content-addressed directory under the phase's Rust authority root,
validates it, then publishes the directory by rename. Directory/file modes are
555/444. Existing copies are reused only after validation. The receipt records
both source and copied-library hashes. Global rustup files remain unchanged.

Only Rust Cargo phases receive this private directory as `DYLD_LIBRARY_PATH`
inside the cleared environment. Helper bytes, source and copied-library bytes,
canonical paths, modes, and loaded LLVM version are checked before and after
each Cargo boundary. A stripping-failure warning fails the phase even if Cargo
returns success. External LLVM 23 clang/lld selection remains independent.

## Focused verification

`sh scripts/check/check-macos-rust-objcopy-authority.shs` builds a tiny offline
static library with a build script. The build script is essential: the static
library alone does not trigger executable stripping. On the affected toolchain,
the unbound build reproduces the warning/SIGABRT, while the bound build succeeds
without either. The test uses the production environment-forwarding function
and records the exact loaded library path using dyld diagnostics.

Negative checks reject missing/symlinked source libraries, changed helper
identities, incorrect LLVM versions, writable directories/files, extra directory
entries, and tampered copied libraries. Reuse checks preserve the copied file's
inode. The original global library's hash must remain unchanged. A zero-exit
log fixture proves the actual production function rejects a stripping warning.

Initial evidence: `build/native_probe/macos-rust-objcopy.DTywxd` in the isolated
`mac-rust-objcopy-rpath-20260922` checkout. Copy/admission of 143,609,472 bytes took
1.71 seconds with maximum RSS 19,824,640 bytes. The clean tiny Cargo build took
0.38 seconds with maximum RSS 101,515,264 bytes. These are focused local
measurements, not full-bootstrap performance or phase-completion claims.

The production-forwarding test also passed under the accepted strict process
guard: `build/native_probe/rust-objcopy/guarded-production.env` records exit 0,
48 samples, 150,256 KiB peak tree RSS, maximum sample gap 110.04 ms, zero
observer errors/overruns, and quiescent cleanup. Fixture evidence is
`build/native_probe/macos-rust-objcopy.g4Lx1g`. Guard SHA-256:
`a6c85d289e8694328a31bbb7948d414a43f7882d4d8ba3a9e4d5a7c5794347c0`.
The final extra-entry and zero-exit-warning checks have separate focused
evidence in `build/native_probe/rust-objcopy/negative-delta.log`; Cargo was not
rerun for those checks.

Static compatibility check:
`sh scripts/check/check-macos-rust-objcopy-authority.shs --static-rustc <stable-sysroot>/bin/rustc`.
The installed stable Rust 1.94.0 helper (LLVM 21.1.8) has no LLVM dylib
dependency and was admitted without a capsule or loader environment. Evidence:
`build/native_probe/rust-objcopy/static-argv-admission.log`. The dynamic mode and
production forwarding were separately rechecked without Cargo, using the
existing copied library; evidence:
`build/native_probe/rust-objcopy/dynamic-mode-delta-final.log`.

The observer's separate `proc_pidinfo EPERM` failure is not established as a
consequence of this library failure and remains a separate investigation.
