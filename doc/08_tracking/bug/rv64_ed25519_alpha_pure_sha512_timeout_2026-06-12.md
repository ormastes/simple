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

## 2026-06-14 RV64 SSH gate moved to Curve25519/build blockers

The live SSH gate moved beyond the original Ed25519 runtime/pure mismatch in
the current code path:

- The live Ed25519 alpha comparison signs the same inputs on both sides:
  `stable_seed`, `stable_pub`, and `stable_hash`.
- KEXINIT now goes through the generic plain-payload sender so the server signs
  the same payload that OpenSSH receives.
- Live X25519 public-key and shared-secret generation now call the dual-backend
  helpers with explicit `dual_backend_alpha_default_mode()`, so runtime/pure
  mismatches must fail closed.

Current Curve25519 evidence:

```text
SIMPLE_LIB=src src/compiler_rust/target/release/simple check \
  src/os/apps/sshd/ssh_session_kex.spl \
  src/os/crypto/curve25519.spl \
  src/os/crypto/dual_backend.spl

All checks passed (3 file(s))

SIMPLE_LIB=src src/compiler_rust/target/release/simple test \
  test/01_unit/os/crypto/dual_backend_alpha_spec.spl \
  --mode=interpreter --timeout-ms=120000 --clean

Passed: 3
Failed: 0
```

The public pure Simple X25519 path is still not RFC7748-clean:

```text
test/01_unit/lib/crypto/curve25519_rfc7748_spec.spl
small-limb backend: Failed: 7
bigint-safe backend: timed out after 120 seconds on the RFC suite
```

One-vector probe for RFC7748 TV1:

```text
expected: c3 da 55 37 9d e9 c6 90 ...
actual:   91 38 8d bb 3f f0 11 9f ...
```

The latest RV64 SSH live gate could not reach QEMU in the current dirty
workspace:

- Spec precheck: `semantic: undefined field: unknown property or method 'name'
  on Option`.
- Native-build link errors include missing `rt_push_byte`,
  `rt_boot_tcp_send_plain_payload`, `rt_array_new_with_cap_u64`, and
  `rt_typed_words_u32_push`.
- Those symbols exist in
  `src/os/kernel/arch/riscv64/boot/freestanding_runtime.c`, so this is a
  build/closure/link inclusion blocker rather than missing source definitions.

Next tasks:

- Repair pure Simple Curve25519/X25519 against RFC7748.
- Resolve the current native-build freestanding runtime inclusion blocker.
- Rerun the RV64 SSH live gate and confirm it fails closed on any remaining
  X25519 alpha mismatch before continuing to NEWKEYS/auth hardening.

## 2026-06-14 RV64 SSH gate now boots/listens; pure X25519 alpha remains blocker

Focused static gate after replacing `get_scenario("rv64-ssh")` field access
with `scenario_exists("rv64-ssh")` + `scenario_by_name_direct("rv64-ssh")`:

```text
SIMPLE_LIB=src bin/simple test \
  test/03_system/os/rv64_ssh_live_login_in_qemu_spec.spl \
  --mode=interpreter --clean --timeout 120 --sequential

5 examples, 0 failures
```

`doc/06_spec` layout gate remained clean:

```text
find doc/06_spec -name '*_spec.spl' | wc -l
0
```

Native-build/link progress:

- `src/compiler_rust/compiler/src/pipeline/native_project/linker.rs` now allows
  `full_networking_runtime.c` only when `SIMPLE_SSH_LIVE_BUILD_MARKER` is set,
  and skips the older example `baremetal_stubs.c` for the same SSH-live lane.
- RISC-V helper files restored under
  `examples/09_embedded/simple_os/arch/riscv64/boot/` for X25519, SHA-512,
  Ed25519 scalar/signing, and SHA-256.
- `src/os/kernel/arch/riscv64/boot/freestanding_runtime.c` gained
  `rt_array_concat` and a freestanding no-op `rt_pool_safepoint`.
- Legacy VirtIO-net negotiation now mirrors the x86 legacy path by advertising
  only `VIRTIO_NET_F_MAC` and skipping the VirtIO 1.0 `FEATURES_OK` transition.

Latest live evidence:

```text
[build][riscv64] phase=native-build OK
[build][riscv64] phase=artifact OK marker=ssh-live-build:cranelift:...
[net-riscv] Network device ready
[net-riscv] Network packet TX ready
[net-riscv] Network probe passed
[net-riscv] TCP bind probe passed
[sshd] SSH daemon listening on port 22
[sshd-session] negotiated kex=curve25519-sha256 hostkey=ssh-ed25519
[sshd-session] server public generation start
X25519 PUB ENTER
X25519 PUB COPIED
X25519 PUB BOOTSTRAP
[sshd-session] x25519 public runtime len=32
[sshd-session] x25519 public pure start
```

The live probe was stopped after reaching the pure Simple X25519 alpha leg.
The current blocker is no longer boot, link, network bring-up, or SSH listen;
it is the pure Simple X25519 implementation/performance/correctness path needed
for alpha runtime-vs-pure comparison.

## 2026-06-14 cautious QEMU memory run: live gate reaches alpha mismatch

The RV64 SSH live gate now runs under a guarded QEMU command with host memory
sampling and no observed memory pressure:

```text
SIMPLE_TEST_TIMEOUT=900 SIMPLEOS_RV64_SSH_LIVE=1 \
SIMPLE_OS_BUILD_BACKEND=cranelift SIMPLE_LIB=src \
bin/simple test test/03_system/os/rv64_ssh_live_login_in_qemu_spec.spl \
  --mode=interpreter --clean --timeout 900 --sequential
```

Latest guarded evidence:

- QEMU run completed in about 46s and failed normally, not by OOM.
- Test wrapper max RSS: about 154 MiB.
- QEMU RSS: about 70 MiB.
- Host memory remained above 115 GiB available; swap stayed at about 82 MiB used.
- Native build, artifact creation, VirtIO network, TCP bind, SSH daemon listen,
  version exchange, KEXINIT negotiation, and OpenSSH connection all succeeded.

Alpha comparison is now explicit in the live X25519 and Ed25519 paths:

- `src/os/apps/sshd/ssh_session_kex.spl` runs runtime/C and pure Simple X25519
  public/shared computations, logs the dual-backend diff, and explicitly
  refuses mismatched output.
- `src/os/apps/sshd/ssh_session_kex.spl` runs runtime/C and pure Simple
  Ed25519 signing and explicitly refuses mismatched signatures.
- `src/os/crypto/dual_backend.spl` compares and formats `[u8]` through
  `rt_bytes_u8_at`, avoiding direct byte-array indexing artifacts on RV64.
- `src/os/crypto/curve25519_smalllimb.spl` now reads byte-array inputs through
  `rt_bytes_u8_at` and avoids indexed byte writes in its output serializer.

Current live blocker:

```text
[dual-backend] curve25519:rv64_live_public: runtime/pure mismatch
[dual-backend] curve25519:rv64_live_shared: runtime/pure mismatch
[dual-backend] ed25519:sign_live: runtime/pure mismatch
```

The pure Simple X25519 implementation still passes RFC 7748 vectors under the
interpreter, but RV64 live output does not match the C/runtime helper for the
bootstrap scalar or OpenSSH client shared secret. The next fix should target
the RV64 codegen/runtime behavior for pure Simple X25519 arithmetic or byte
array mutation, not the QEMU/network/SSHD startup path.

## 2026-06-14 X25519 isolation update

Additional focused regression coverage was added to
`test/01_unit/lib/crypto/curve25519_rfc7748_spec.spl` for the RV64 SSH live
bootstrap scalar:

```text
private = 489c2a61f53317b82d74a10ecc5983429106df38be2765aa14e7904b6c21d37f
public  = 8c16c1dd75b797a29ba2c17eb5a768e44a760b9a0d0f8c5972cafb72efe10337
```

Interpreter evidence:

```text
SIMPLE_LIB=src timeout 180 bin/simple test \
  test/01_unit/lib/crypto/curve25519_rfc7748_spec.spl \
  --mode=interpreter --timeout-ms=180000 --clean

9 examples, 0 failures
```

Both the public small-limb API and the independent BigInt probe match the live
C helper's bootstrap public key under the interpreter. A diagnostic live run
using the BigInt probe as the pure oracle did not finish the public-key pure
leg before the host SSH probe timed out, so BigInt is correct but not viable as
the live KEX alpha oracle without a separate timeout/probe design.

The small-limb backend was hardened to reduce RV64-sensitive byte/numeric
surfaces:

- byte-array input reads use `rt_bytes_u8_at`;
- output serialization avoids indexed byte writes;
- base-point construction avoids a `[u8]` literal;
- carry propagation uses exact division by radix constants instead of `>>`.

Latest guarded QEMU evidence still fails closed at the first X25519 alpha
mismatch:

```text
[dual-backend] curve25519:rv64_live_public: runtime/pure mismatch
  runtime=8c16c1dd75b797a29ba2c17eb5a768e44a760b9a0d0f8c5972cafb72efe10337
  pure=5a0407dc977b896e0a00fbd580a29103d92d00363c1060c929c0fb72af0fdc00
[sshd-session] x25519 public alpha mismatch: refusing runtime output
[sshd-session] server public generation len=0
[sshd-session] disconnect reason=2 desc=server X25519 public failed
```

Memory remained safe in the latest run: QEMU RSS about 64 MiB, wrapper max RSS
about 121 MiB, no swap growth. The current root cause is narrowed to RV64
native execution of the pure small-limb X25519 arithmetic path.

### Follow-up diagnostics

Additional RV64 live diagnostics:

- Replacing the ladder bit test with division/modulo changed the wrong RV64
  pure result to `0408057894aef06c60003c8d80c3df0129a8050e831cb00327208fd2157c1a00`.
- Replacing the ladder bit test with comparison/subtraction restored the
  earlier wrong RV64 pure result
  `5a0407dc977b896e0a00fbd580a29103d92d00363c1060c929c0fb72af0fdc00`.
- A live diagnostic using the older 5-limb `x25519_base_fe_probe` as the pure
  public-key oracle did not complete before the host SSH KEX timeout, similar
  to the BigInt probe. It is not viable for the live alpha gate without a
  separate non-handshake probe design.

The latest evidence points at native RV64 lowering/runtime behavior for the
small-limb ladder/arithmetic path. SSH framing remains protected by the
fail-closed alpha guard.

### Standalone QEMU probe with memory guard

Added `examples/09_embedded/simple_os/arch/riscv64/x25519_probe_entry.spl` as
a non-handshake RV64 boot entry that computes the bootstrap X25519 public key
and compares it against the known runtime/C value.

Build/check evidence:

```text
SIMPLE_LIB=src bin/simple check \
  examples/09_embedded/simple_os/arch/riscv64/x25519_probe_entry.spl \
  src/os/crypto/curve25519_smalllimb.spl src/os/crypto/curve25519.spl

All checks passed (3 file(s))
```

QEMU memory-guard evidence:

```text
timeout 15 qemu-system-riscv64 -machine virt -cpu rv64 -m 1024M \
  -serial stdio -display none -no-reboot \
  -kernel build/os/simpleos_riscv64_x25519_probe.elf -bios default

qemu_exit=124
max_wrapper_rss_kb=2140
max_qemu_rss_kb=56080
SwapTotal:=8388604 SwapFree:=8304328
```

The standalone probe booted but did not complete X25519 before the cautious
timeout. No matching QEMU process was left after timeout. This keeps the next
diagnostic path outside SSH while avoiding unbounded memory or process growth.

Follow-up on the standalone probe build profile:

```text
SIMPLE_LIB=src bin/simple test \
  test/01_unit/lib/crypto/curve25519_rfc7748_spec.spl \
  --mode=interpreter --timeout-ms=180000 --clean

10 examples, 0 failures
```

The spec now covers the shallow small-limb helpers used by the probe:
bootstrap scalar clamp, base-point construction, base-point mask, and
field encode/decode roundtrip.

Direct ad hoc `native-build` invocations are not reliable evidence for this
RV64 probe:

- without `SIMPLE_BOOT_MINIMAL=1`, QEMU enters a generated start stub but the
  Simple serial markers do not print;
- with `SIMPLE_BOOT_MINIMAL=1`, the minimal profile omits typed array helpers
  required by pure X25519;
- with `SIMPLE_BOOT_MINIMAL=1` plus the SSH-live marker, the probe links
  against the live helper set but does not emit probe markers within 25s and
  QEMU RSS climbs to about 269 MiB before timeout.

The next standalone diagnostic should be registered as a first-class RV64
crypto probe lane in the QEMU runner/native build profile instead of using
one-off shell build flags.

### 2026-06-14 RV64 X25519 serializer fix

Registered `rv64-x25519-probe` as a first-class QEMU runner scenario using
`examples/09_embedded/simple_os/arch/riscv64/x25519_probe_entry.spl` and the
same RV64 live-helper build profile as the SSH lane.

Root cause isolated by the probe:

- RV64 native `x25519_smalllimb_roundtrip_probe(BASE_POINT)` returned all
  zeros before the fix.
- Interpreter coverage returned the correct base point.
- `_x25519_fe_to_bytes` still mutated a `[u64]` limb array with indexed
  stores (`h[0] = ...`, `h[1] = ...`). Replacing those array mutations with
  local limb variables fixed RV64 native serialization.

Focused interpreter evidence after the fix:

```text
SIMPLE_LIB=src bin/simple test \
  test/01_unit/lib/crypto/curve25519_rfc7748_spec.spl \
  --mode=interpreter --timeout-ms=180000 --clean

10 examples, 0 failures
```

Canonical runner build evidence:

```text
SIMPLE_LIB=src SIMPLE_OS_LOG_MODE=on \
  bin/simple os build --scenario rv64-x25519-probe --log on

[build][riscv64] phase=native-build OK
[build][riscv64] phase=artifact OK marker=ssh-live-build:cranelift:...
```

Guarded QEMU evidence after the fix:

```text
X25519_PROBE_ROUNDTRIP=0900000000000000000000000000000000000000000000000000000000000000
X25519_PROBE_ACTUAL=8c16c1dd75b797a29ba2c17eb5a768e44a760b9a0d0f8c5972cafb72efe10337
X25519_PROBE_EXPECTED=8c16c1dd75b797a29ba2c17eb5a768e44a760b9a0d0f8c5972cafb72efe10337
X25519_PROBE_FULL_DONE
max_wrapper_rss_kb=2192
max_qemu_rss_kb=57180
SwapTotal:=8388604 SwapFree:=8304360
```

`bin/simple os run --scenario rv64-x25519-probe --log on` now returns status
0 and accepts the `X25519_PROBE_FULL_DONE` marker.

Latest RV64 SSH live evidence after the serializer fix:

```text
[sshd] SSH daemon listening on port 22
[sshd] accept loop start
Process timed out
[run] FAILED (exit code -1)
```

The earlier X25519 alpha mismatch no longer appears before listen. The next
SSH hardening issue is the live-runner/host-probe path timing out after the
daemon reaches listen.

### 2026-06-14 RV64 SSH host-probe and Ed25519 alpha evidence

Added host and guest diagnostics to the RV64 SSH lane:

- `src/os/ssh_qemu_contract.spl` now prints host-side readiness, OpenSSH
  start/exit, and marker status.
- `src/os/apps/sshd/sshd.spl` now emits low-rate accept-loop wait markers.
- `src/os/_QemuRunner/scenario_exec.spl` gives `rv64-ssh` a 300s scenario timeout on
  both `os test` and `os run` paths.

Guarded OpenSSH-backed QEMU evidence:

```text
status=1
rss=Maximum resident set size (kbytes): 125836
qemu_before_exact=
qemu_after_exact=
[ssh-host] ready=1
[sshd] accepted client fd=200
[sshd-session] x25519 public runtime len=32
[sshd-session] x25519 public pure len=32
[sshd-session] shared secret generation len=32
```

This proves the previous networking hypothesis was too broad: host TCP
connects, the guest accepts the client, X25519 public-key parity completes,
and the X25519 shared secret is produced.

Current fail-closed blocker:

```text
[ed25519] live sha512 mismatch label=seed len=32
[ed25519] live sha512=357c83864f2833cb427a2ef1c00a013cfdff2768d980c0a3a520f006904de90f9b4f0afe280b746a778684e75442502057b7473a03f08f96f5a38e9287e01f8f
[ed25519] pure sha512=0e8fc0447185a17df54bc0a2429ea4d9f2d12c1e4a28ead1f949c65d4b92638e0f2d352c951861b9f03bc6bdb3a279870776921cbe8c6eab0f4ccedf732489eb
[dual-backend] ed25519:sign_live: runtime/pure mismatch
[sshd-session] ed25519 alpha mismatch: refusing runtime signature
```

The live C SHA-512 value equals Python/OpenSSL SHA-512 for the RFC8032 test
seed. The divergent value is the RV64 native execution of the pure Simple
`std.crypto.sha512_bytes` path used by Ed25519. The alpha guard is therefore
correctly refusing to serve SSH with a runtime/pure signing mismatch.

Added `test/01_unit/os/crypto/sha512_direct_kat_spec.spl` coverage for the
RFC8032 seed hash so the OS-local SHA-512 implementation has the exact live
seed vector in addition to empty and `abc`.
