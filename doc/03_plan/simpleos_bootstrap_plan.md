# SimpleOS Bootstrap Plan

Status: active
Date: 2026-04-24

## Goal

Prove that the Simple compiler can be built and verified for SimpleOS guest targets with a repeatable staged pipeline, and preserve a clear path to in-guest self-host convergence.

## Phases

### Phase 1: Sysroot and Runtime Prerequisites

- Build the SimpleOS sysroot with `src/os/port/llvm/sysroot.shs`
- Ensure `libsimpleos_c.a`, `crt0.o`, headers, and `simpleos.ld` are present under `build/os/sysroot/`
- Verify target metadata comes from `src/os/port/simpleos_native_build_config.spl` and `src/os/port/simpleos_multiplatform_build.spl`

### Phase 2: Host-Driven Cross Bootstrap

- Use `src/os/port/bootstrap_cross.spl` to build the seed, stage1, stage2, and stage3 compiler artifacts for the `simpleos-x86_64` bootstrap selector (guest lane `x86_64-simpleos`)
- Package staged outputs when required for deployment or guest testing
- Compare stage2 and stage3 outputs and inspect auto-stub counts when byte identity is not yet available

### Phase 3: Host Verification Gate

- Use `src/os/port/bootstrap_verify.spl` for prerequisite and convergence checks
- Use `src/os/port/verify_all.spl` for dry-run and toolchain/bootstrap readiness scans
- Require native-surface regression checks through `src/os/port/native_surface_policy_verify.spl`

### Phase 4: In-Guest Self-Host Convergence

- Use `src/os/port/bootstrap_native_verify.spl` once the guest can execute `/bin/simple native-build`
- Build stage2 and stage3 inside SimpleOS and compare outputs directly
- Treat matching binaries as the strongest convergence signal; otherwise require equivalent symbol/stub diagnostics before accepting the run

## Acceptance

- Toolchain dry-run verification passes
- Bootstrap prerequisite verification passes
- Cross bootstrap can produce stage2 and stage3 artifacts for the selected bootstrap selector and its underlying guest lane
- Native-surface policy verification passes for the covered SimpleOS reduction scope
- In-guest native convergence path remains documented and executable when guest-side prerequisites are available
