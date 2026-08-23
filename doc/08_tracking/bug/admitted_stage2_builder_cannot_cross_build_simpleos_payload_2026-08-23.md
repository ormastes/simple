# Stage-2-admitted builder cannot cross-build the SimpleOS guest payload (2026-08-23)

Status: OPEN — honest block. Nothing was forced, stubbed, or bypassed.

## Summary

The SimpleOS guest-toolchain lane (`scripts/os/provision_simpleos_guest_simple_fs.shs`
-> `scripts/check/check-simpleos-fs-toolchain-qemu-matrix.shs`) requires a
target-native `aarch64-unknown-simpleos` ELF payload built by a Stage-2-admitted
pure-Simple compiler. On this host (macOS arm64, 2026-08-23) the **admission half
is satisfied** and the **capability half is not**: the only admitted builder is the
*bootstrap* CLI, whose `native-build` has no cross-target surface at all.

## Evidence — admission: PASS

Admitted builder and adjacent receipt:

- `/Users/ormastes/simple/build/bootstrap/stage3/aarch64-apple-darwin/stage2-admitted/simple`
  — Mach-O 64-bit arm64, 138,591,704 bytes, mtime 2026-08-23T19:31:44Z,
  sha256 `708f9fa89c8f462dd643bd294b2bc1329d3a7da7e9b57c75bc6f8d08d6823c3f`
- `.../stage2-admitted/admission.env` — 1,471 bytes,
  sha256 `4e51fabca2516030654d3fad2c14156ef4b5e5041142041477c9356c598e9102`,
  `schema=simple-bootstrap-stage2-admission-v1`, `status=admitted`,
  `admission_identity=559f8a09edd44b888338602b5b3be712cfb279ef843b4007ae95fa059608ceea`,
  `checks_executed_at_admission=1`, `checks_replayed_during_stage3=0`

Verified by the provisioner's own entry point (absolute paths required —
`bootstrap_stage3_canonical_path`, `scripts/check/lib/bootstrap-stage3/authority.shs:139-144`,
rejects relative input):

```
sh scripts/os/provision_simpleos_guest_simple_fs.shs --validate-builder <builder> <admission.env>
-> simpleos_guest_simple_builder_authority_status=pass   (rc 0)
```

That exercises `verify_builder_authority` (`scripts/os/provision_simpleos_guest_simple_fs.shs:20-36`)
and `bootstrap_stage3_verify_stage2_admission_receipt`
(`scripts/check/lib/bootstrap-stage3/sanity.shs:242`) end to end.

## Evidence — capability: FAIL (the actual blocker)

`scripts/os/simpleos-native-build-aarch64.shs:41` selects its builder through
`simple_compiler_select --builder-target aarch64-unknown-simpleos`. The admitted
binary passes identity and the environment-write probe and fails the builder tier:

```
simple_compiler_is_seed       -> rc 1  (not the seed)
simple_compiler_env_write_ok  -> rc 0  (usable core tier)
simple_compiler_can_build_target <bin> aarch64-unknown-simpleos -> rc 1
```

`simple_compiler_can_build_target` (`scripts/lib/simple-compiler-select.shs`)
requires the `Simple Native Build` banner and an advertised `--runtime-bundle`.
The admitted binary answers instead:

```
$ <builder> --help
Simple Bootstrap Compiler v1.0.0-RC
Commands:
  compile <file> --format=smf
  native-build <file>.spl

$ <builder> native-build --target aarch64-unknown-simpleos --help   # rc 0
Usage: simple native-build <file>.spl [-o <output>] [--backend=...] [--mode=...]
       [--no-borrow-check] [--entry <file>] [--source <dir>] [--list-optimizations] [-h]
```

`--target` is accepted without error on the `--help` path but appears nowhere in
the advertised surface (whether a real build would ignore or reject it is
UNVERIFIED — no cross-target build was attempted). **None** of `--target`,
`--runtime-bundle`, `--linker-script`, `--entry-closure` are advertised; all four
are required by `simpleos-native-build-aarch64.shs:76,78,79,82`. It is the bootstrap CLI
(`src/app/cli/bootstrap_main.spl`), which by design exposes only `compile` and
`native-build`; a host-target build is the only thing it can do.

## Consequent state

- No `*.build_stamp` exists anywhere under `build/`.
- The whole aarch64 SimpleOS sysroot is absent: `build/os/sysroot-aarch64/{lib/crt0.o,
  lib/libsimpleos_c.a, lib/libsimpleos_all.a, lib/cc-aarch64-simpleos,
  share/simpleos/simpleos.ld}` and `build/os/simple-core-simpleos-aarch64/libsimple_runtime.a`.
- `build/os/` holds only `aarch64_limine/` and `rv64_opensbi_realfw_probe/`.
- Matrix verdict, arm64, measured: `simpleos_fs_toolchain_matrix_status=blocked`,
  rc 3, per-cell reason
  `target-native-simple-filesystem-receipt-unavailable:aarch64-unknown-simpleos`;
  provisioner log line: `receipt missing: build/os/fat32-arm64.img.simple-toolchain.sdn`.

## What would satisfy it

A Stage-2-admitted, **full-CLI** pure-Simple compiler — i.e. a deployed stage that
dispatches the full `native-build` surface (`--target`, `--runtime-bundle`,
`--linker-script`, `--entry-closure`), with an adjacent `admission.env`. Then, in
order: `scripts/os/simpleos-sysroot-aarch64.shs`, the aarch64 `simple-core` runtime
archive, `scripts/os/simpleos-native-build-aarch64.shs`, then the provisioner.

## Ceiling beyond this blocker (UNVERIFIED as a separate defect, but read from source)

Even a fully staged receipt cannot make this matrix go live today:
`scripts/check/check-simpleos-compiler-filesystem-qemu.shs:128` hardcodes
`GUEST_WORKFLOW_READY=0` and exits 3 `blocked` with reason
`arm64-compiler-filesystem-guest-workflow-not-wired`. Clearing that needs a
production caller for `compiler_filesystem_guest_workflow_v2`. Flipping the flag
without that caller would be gate-weakening and must not be done.

## Host-portability defects found and fixed in passing (uncommitted)

1. `scripts/os/provision_simpleos_guest_simple_fs.shs` — `validate_target_elf`
   hardcoded `readelf`, absent on macOS; the lane died with `readelf is required`
   even though `/opt/homebrew/opt/llvm/bin/llvm-readelf` is installed. Replaced with
   `discover_readelf()` (`$READELF`, `readelf`, `llvm-readelf`, `eu-readelf`, then
   the two Homebrew keg paths), fail-closed when none is found. Executed on this
   host against `build/os/aarch64_limine/kernel.elf`: resolves to
   `/opt/homebrew/opt/llvm/bin/llvm-readelf` (rc 0), `-h` prints `Class: ELF64`,
   `-l` yields 0 INTERP entries — both greps the caller relies on are satisfied.
2. Same file — `run_self_test` did `cp /bin/true`, which does not exist on macOS,
   so `--self-test` exited 1 on this host with `cp: /bin/true: No such file or
   directory`. Now discovers a real `true` binary and fails closed. Measured after
   the fix: `simpleos_guest_simple_fs_authority_self_test=pass forged_stamp=reject
   forged_receipt=reject` (rc 0).
3. `scripts/os/simpleos-native-build-aarch64.shs` — same hardcoded `readelf` in its
   `[verify]` step, now discovered fail-closed; and `OUTPUT` is now overridable via
   `$SIMPLEOS_PAYLOAD_OUTPUT` (`:28`, default unchanged) so a lane forbidden from writing
   under `bin/release/**` can stage the payload elsewhere.
