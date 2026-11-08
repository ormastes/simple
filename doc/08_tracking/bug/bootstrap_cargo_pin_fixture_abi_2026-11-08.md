# Cargo pin fixture omitted Windows ABI

Status: fixed; focused shell regression PASS. Full bootstrap remains unverified.

At source 3eda0f35875c9cc2f0d1697886c5100ea49ff7e5, running `sh scripts/check/check-bootstrap-cargo-toolchain-pins.shs` exits nonzero with `PLATFORM_ABI: unbound variable`. The extracted production environment owner checks the Windows ABI; the Windows fixture did not provide it under `set -u`.

The fixture now invokes the real extracted owner for both `msvc` and `gnu`, retaining assertions that unset CXX, AR and RUSTFLAGS remain unset. This covers the missing setup for both supported Windows dialects without changing production defaults. The corrected harness passes its LLVM pin negative controls, compiler selection checks, four Cargo branches and Windows environment checks. This is a hermetic harness result, not Windows execution or compiler qualification.
