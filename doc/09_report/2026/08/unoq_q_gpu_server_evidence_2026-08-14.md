# UNO Q GPU server evidence receipt — 2026-08-14

Status: **WARN (blocked)**

This receipt is tied to repository revision
`8884df02847316906feda5c8ae39c0f65c3a136e` and live ADB serial
`3655308719`.  Collection completed at `2026-08-14T04:38:21Z`.  Every board
command was serialized by `/tmp/unoq-server-matrix.lock`; no board file was
created or modified.

## Device identity

- Kernel: `Linux uno-q 6.16.7-g0dd6551ae96b ... aarch64 GNU/Linux`
- Device-tree model: `Arduino SA,Imola`
- Userspace: Debian GNU/Linux 13 (trixie)
- Boot identity: `e5bd8b78-9719-4a98-acba-11a0ef34980e`
- GPU node: `/dev/dri/renderD128`
- Vulkan physical GPU: `Turnip Adreno (TM) 702`, integrated GPU, Mesa Turnip
  25.2.6
- Vulkan CPU device: `llvmpipe (LLVM 19.1.7, 128 bits)`

These facts prove a physical UNO Q board and a board-native Vulkan-capable
Adreno device.  They do **not** prove SimpleOS execution: the board is running
Debian userspace and must not be described as SimpleOS.

## Canonical live gate

Command (with the lock held):

```text
sh scripts/check/run-unoq-qrb2210-native-2d-live.shs \
  --device 3655308719 \
  --output-dir build/unoq-server-matrix/gpu-live
```

Result (exit 2):

```text
unoq_native_2d_live_status=blocked
unoq_native_2d_live_reason=pure-simple-runtime-missing
unoq_native_2d_live_evidence_class=live-runner-owned
```

Runner SHA-256:
`28974d6a31f186da8d77a0eb8415276fbb31cef23f8bcc32ebb6e1aa98e8b951`.
Captured gate-log SHA-256:
`9797668b837e5ca35a599447886ab8bb5821c79f0956a0bee73f6e76232a9e5b`.

An independent read-only device check also found the required production
provider `/usr/bin/simpleos-unoq-2d-evidence` absent.  Consequently there is no
provider binary to hash and no admissible provider receipt or capture.

## Acceptance disposition

The GPU criterion is blocked.  No receipt proves SimpleOS backend selection,
command submission, fence completion, device readback/checksum, or continued
web/database/filesystem-server liveness.  CPU-only versus GPU timing is also
not admissible until the same real server executable can run in both explicitly
selected modes.  `vulkaninfo` device discovery is diagnostic evidence only and
is not promoted to execution evidence.

The required ownership contract remains: the parent process exclusively owns
mutable web, database, and filesystem state; the GPU receives only a copied or
frozen encoded workload (or a generation-bound validated device handle); the
GPU returns a bounded pointer-free result receipt; and the parent validates the
generation, completion fence, byte count, and checksum before deterministic
commit.  Neither raw pointers nor GPU-side mutation of canonical server state
are admissible.  Because no production provider ran, this boundary was not
exercised and receives no acceptance credit.

Exact blockers:

1. The provenance-verified full Pure-Simple host runtime required by the live
   gate is unavailable.
2. The physical board's canonical SimpleOS evidence provider is absent.
3. The connected board runs Debian, not the unavailable physical SimpleOS
   QRB2210 port/runtime.
4. No real SimpleOS web/database/filesystem server was live for CPU/GPU
   comparison.
