# Windows SHA-256 report method binding

Status: source mitigation proposed; native verification UNRUN.

The Windows resume2 phase3-16 compilation of
`src/app/bootstrap_builder/native_group_linux_launcher.spl` reports
`unresolved method call: verified at src/lib/common/crypto/sha256.spl:24:9`.
Evidence is recorded in
`D:/dev/bootstrap-failure-catalog-20261002/windows-resume2/evidence.json`;
the log is under
`D:/dev/windows-release-7734-build-20261002/phase34-diagnostic-resume2/phase3/llvm/modules/work/attempt.uEL7zD/16/compile.log`.
The frozen failed source is `7734f947be8ba9465d0ba312170681074e990587`.

At candidate `00b1923fe2e624a26c6b3f1534327d21efc41a83`, five inferred
locals in SHA-256 receive `SecureZeroReport` from an imported function, but
the module imports only that function. Each then calls `verified()`.
The existing native SHA-256 regression explicitly imports and annotates
`SecureZeroReport` for its equivalent direct call. This change gives the
five production locals the same explicit binding. It retains every volatile
wipe, readback, and fail-closed check; no cryptographic arithmetic changes.

Compiler debt remains: a function's declared return type should suffice to
resolve methods without this explicit import/annotation. The precise compiler
inference failure is unproven until an isolated before/after native reproduction
is admitted. The diagnostic line is not a precise call-site locator.
This is a bounded source mitigation, not a claim that the compiler is fixed.

The existing `sha256_method_binding_main.spl` fixture retains fixed SHA-256
vectors and actual wipe readback, and now checks streaming zeroization,
every state/block/schedule slot, and rejection of updates after zeroization.
Native compilation and execution must both succeed and print
`SHA256_METHOD_BINDING_NATIVE_PASS` before marking this failure resolved.

Runtime verification is UNRUN: the parent requires resource admission before
new compiler/native/WSL jobs. No build or cache was started or modified.
The contracts.lower failure and all other inventory failures remain open.
