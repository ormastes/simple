# RV64 SSH alpha Ed25519 runtime/pure mismatch

Date: 2026-06-12
Status: open
Area: SimpleOS RV64 SSH, crypto dual-backend alpha

## Summary

The RV64 live OpenSSH gate reaches SSH KEXINIT parsing, Curve25519 ECDH, shared
secret generation, exchange-hash generation, and now completes the pure-Simple
Ed25519 signing side. The current alpha blocker is no longer the pure SHA-512
nonce-hash timeout; it is a runtime/pure signature mismatch.

Alpha mode is behaving as designed: it runs the runtime/C-backed signature path
and then the pure-Simple signature path before comparing outputs. The runtime
side returns a 64-byte signature. A fixed RFC 8032 seed-expansion helper moved
the live lane past SHA-512(seed), Ed25519 now calls the direct
`os.crypto.sha512.sha512` implementation for `[u8]` input, and the pure side
completes both the nonce and challenge SHA-512 hashes. The pure signature
currently becomes 64 zero bytes in the live RV64 lane, while the runtime side
returns a nonzero 64-byte signature.

## Reproduction

```bash
SIMPLEOS_RV64_SSH_LIVE=1 SIMPLE_LIB=src \
  src/compiler_rust/target/release/simple test \
  test/03_system/os/rv64_ssh_live_login_in_qemu_spec.spl \
  --mode=interpreter --timeout 900 --clean
```

Latest observed result:

- Test file: `test/03_system/os/rv64_ssh_live_login_in_qemu_spec.spl`
- Result after RV64 SSH marker rebuild fix and freestanding SHA-512 cleanup:
  native-build succeeds and OpenSSH receives `SSH2_MSG_KEX_ECDH_REPLY`, but the
  Ed25519 host signature is invalid because alpha detects runtime/pure mismatch.
- Build artifact log:
  `build/test-artifacts/03_system/os/rv64_ssh_live_login_in_qemu/combined.log`
- Latest signature-mismatch serial timestamp: 2026-06-12 06:34:24 UTC
- A TCP hardening patch now ignores SYN packets while an accepted client is
  already open, before mutating peer state. The latest run reached Ed25519
  again instead of stopping at the intermittent `no KEXINIT received` boundary.
- Focused reproduction without SSH:
  `examples/09_embedded/simple_os/arch/riscv64/ed25519_probe_entry.spl`
  built as `build/os/simpleos_riscv64_ed25519_probe.elf` and run under QEMU.
  It reproduces the same signature-stage failure on RFC 8032 test vector 1.

## Evidence

Relevant fresh serial boundary:

```text
[sshd-session] exchange hash len=32
[sshd-session] host ed25519 seed len=32 pub len=32
[sshd-session] host ed25519 sign pure start
[sshd-session] ed25519 alpha runtime start
[sshd-session] ed25519 alpha runtime done len=64
[sshd-session] ed25519 alpha pure start
[ed25519] sign: fixed seed hash start
[ed25519] sign: fixed seed hash done
[ed25519] sign: nonce hash done
[ed25519] sign: R scalar mul start
[ed25519] sign: R scalar mul done
[ed25519] sign: R encode done
[ed25519] sign: challenge hash start
[ed25519] pure sha512: hash start
[ed25519] pure sha512: hash done
[ed25519] sign: challenge hash done
[ed25519] sign: S muladd start
[ed25519] sign: S muladd done
[ed25519] trace r len=32 nz=8 first=72 last=0
[ed25519] trace r_enc len=32 nz=0 first=0 last=0
[ed25519] trace k len=32 nz=8 first=200 last=0
[ed25519] trace s len=32 nz=3 first=64 last=0
[ed25519] trace s_copy len=32 nz=2 first=0 last=0
[ed25519] sign: done
[ed25519] trace sig len=64 nz=0 first=0 last=0
[sshd-session] ed25519 alpha pure done len=64
[dual-backend] ed25519:sign_live: runtime/pure mismatch | inputs=seed_len=32;pub_len=32;msg_len=32 | runtime=... | pure=00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
[sshd-session] ed25519 alpha mismatch: refusing runtime signature
[sshd-session] host ed25519 sign pure len=0
```

This confirms the earlier TCP plaintext framing failure is past the gate: the
server now receives OpenSSH KEXINIT and KEX_ECDH_INIT payloads and computes the
exchange hash before the Ed25519 alpha mismatch becomes the limiting step.

Additional build evidence from the optimization attempt:

```text
Build failed: link failed: ld.lld: error: undefined symbol: rt_sha512_H
>>> referenced by simple_module
>>>               /tmp/.tmpy6Z8K4/mod_31.o:(os__crypto__sha512___sha512_pure_simple)
```

The direct cause was a legacy `_sha512_pure_simple` helper still calling the
runtime extern `rt_sha512_H`. That helper now uses the local `_sha512_h`
constants, which makes the module freestanding-clean. Separately, attempted
K-table and `t << 3` optimizations also emitted the same unsupported symbol and
were reverted.

## Non-fixes

- Do not switch the live gate to `normal` mode to bypass the pure side.
- Do not replace the pure-Simple Ed25519 path with C/Rust and still call it
  alpha parity.
- Do not use the previous K-table or `t << 3` optimization shapes until they
  are separately proven in RV64 freestanding native-build.
- Do not accept a runtime signature after alpha logs a mismatch.

## Required fix

Keep alpha semantics intact and fix the RV64 pure-Simple Ed25519 signing path
so it byte-matches the runtime signature. The next focused suspects are scalar
reduction/muladd, point encoding, and byte-array copy/read behavior in
freestanding RV64:

- `r` and `k` are nonzero but sparse after scalar reduction.
- `r_enc` is all zero after `ed_scalar_mul_basepoint(r)` and `ed_point_encode`.
- `s` is nonzero after `sc_muladd(k, a, r)`.
- Copying `s` into another 32-byte array preserves only part of its nonzero
  content.
- The final 64-byte signature currently reads as all zero.
- Replacing `_small_ed_cached_select_16_pair` with direct table indexing did
  not change the RV64 probe result, so the cached constant-time selector is not
  the immediate cause of the zero `r_enc` boundary.

Also keep tracking the intermittent TCP receive path separately from the
Ed25519 parity bug; the current SYN guard reduced one observed `no KEXINIT`
failure mode.

## 2026-06-12 focused RV64 probe update

Focused target:

```bash
SIMPLE_LIB=src SIMPLE_BOOT_MINIMAL=1 SIMPLE_OS_LOG_MODE=on PATH="/usr/bin:$PATH" \
  src/compiler_rust/target/debug/simple native-build \
  --source build/os/generated --source src --source examples \
  --backend cranelift --opt-level=aggressive --log on --timeout 180 \
  --entry-closure \
  --entry examples/09_embedded/simple_os/arch/riscv64/ed25519_probe_entry.spl \
  --target riscv64-unknown-none \
  -o build/os/simpleos_riscv64_ed25519_probe.elf \
  --linker-script examples/09_embedded/simple_os/arch/riscv64/linker.ld

timeout 120 qemu-system-riscv64 -machine virt -cpu rv64 -m 512M \
  -nographic -serial mon:stdio -bios default \
  -kernel build/os/simpleos_riscv64_ed25519_probe.elf
```

New layer evidence:

- `ed_point_encode(_ed25519_base_point())` now passes after `fe_to_bytes`
  stopped using indexed `[u8]` writes and Ed25519 basepoint/`d` constants moved
  to direct 51-bit limbs.
- Raw table entry `1*B` now passes after table generation seeds entry 1 from
  the base point instead of computing `identity + base`.
- `ed_scalar_mul_basepoint([1, 0, ...])` now passes through the simple
  correctness path.
- Cached `identity + B` still fails (`got=107`, expected `88` at byte 0), so
  the cached add path must not be used to seed the first nonzero scalar digit.
- SHA-512 empty KAT fails on RV64 before Ed25519 signing:

```text
[ed25519-probe] sha512-empty len=64
[ed25519-probe] sha512-empty FAIL idx=0 got=4 expected=207
```

After switching SHA-512 byte input reads to `rt_bytes_u8_at`, the empty KAT
still fails and RFC 8032 test 1 still mismatches. The current first blocker is
therefore RV64 correctness of the pure SHA-512 core/state/schedule, not SSH
framing or Ed25519 basepoint encoding.

## 2026-06-12 Ed25519 RFC8032 closure update

The current focused Ed25519 lane is now RFC8032-clean on host and passes the
RV64 SimpleOS signing probe.

Fixes applied:

- `_x25519_fe_sq(a)` delegates to `_x25519_fe_mul(a, a)` so field squaring uses
  the RV64-proven multiplication path.
- Pure `_sha512_modl` no longer uses `rt_ed25519_sc_reduce_64`; the pure side
  now hashes and reduces through pure Simple code.
- `sc_reduce` uses a bit-serial modulo-L reducer instead of shifted
  subtraction.
- `ed_point_double` routes through `ed_point_add(p, p)` for correctness.
- `ed_scalar_mul(k, A)` now uses the correctness-first bit ladder. This fixed
  the four remaining positive RFC8032 verification failures from the cached
  arbitrary-point scalar path.

Verification evidence:

```text
SIMPLE_LIB=src src/compiler_rust/target/release/simple test \
  test/01_unit/lib/crypto/ed25519_rfc8032_spec.spl \
  --mode=interpreter --timeout-ms=300000 --clean

Passed: 15
Failed: 0
```

Focused RV64 SimpleOS probe:

```text
[ed25519-probe] sha512-empty PASS
[ed25519-probe] basepoint-encode PASS
[ed25519-probe] cached-identity-add-one-encode PASS
[ed25519-probe] scalar-one-encode PASS
[ed25519] trace r len=32 nz=32 first=243 last=4
[ed25519] trace r_enc len=32 nz=31 first=229 last=85
[ed25519-probe] sign done len=64
[ed25519-probe] PASS
```

Remaining work is to retry the broader RV64 SSH/live stack gate and continue
hardening TCP receive/framing if the next failure is outside Ed25519.
