# SOSIX kernel positioned dispatcher v1

Status: RED (fresh scoped verification, 2026-08-12). The focused diagnostic
executed all 4 scenarios: 2 passed and 2 failed after two bounded fix cycles.
Uninstalled and invalid-owner fail-closed cases pass. The installed-success
path persists the returned buffer mutation but the nested returned owner still
retains request token 11 instead of 12. The authentication/persistent-identity
scenario also remains RED. No production trap wiring is authorized.

This is diagnostic evidence only: the deployed `bin/simple` identifies itself
as the Rust bootstrap seed. The admitted pure-Simple stage at
`/mnt/data/bs2/final-e73-run2/bootstrap/stage3/x86_64-unknown-linux-gnu/stage2-admitted/simple`
identifies as staged Simple source but exposes only `compile` and
`native-build`, not the `test` command. Therefore no pure-Simple test-runner
verdict exists for this spec.

The architecture-neutral kernel/VFS owner installs one ready positioned-I/O
lifecycle value. Before installation, syscalls 134 and 135 fail with ENOTSUP.
After installation, authenticated calls persist registry bytes and advance the
request token. Rejected, unauthenticated, and unrelated syscalls do not consume
that identity. Installation of an incomplete owner fails closed.

The dispatcher does not create a global backend or claim that an architecture
trap path already stores this value. A live owner must explicitly retain the
returned state beside its true positioned VFS backend.

Resume after deploying a pure-Simple full CLI. The private provider rejection
helper has been uniquely named to remove its known cross-module overload
collision; the remaining nested aggregate scalar-retention defect must be
fixed without replacing the persistent owner contract with synthetic state:

`SIMPLE_LIB=src bin/simple test test/01_unit/os/sosix/fs_kernel_positioned_dispatch_v1_spec.spl --mode=interpreter`
