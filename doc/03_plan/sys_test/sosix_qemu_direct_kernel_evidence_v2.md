# SOSIX QEMU direct-kernel evidence v2 test plan

Acceptance requires one fresh RV32 run after schema review. No prior transcript
can be promoted.

- Pre-run host admission is closed and accelerator-probed.
- Transcript orders `guest-entry`, unique nonce, real listing, mounted program
  stdout, exit 37, reap, and final PASS.
- Producer emits schema v2, exact no-firmware tuple, and eight artifacts.
- Collector imports a complete 24-cell source tree and admits RV32 exactly once.
- Sabotage rejects missing external firmware, fake guest-entry, duplicate nonce,
  modified argv, and modified kernel bytes.

Lower-model lane: `N/A` because Spark is unavailable. Merge owner and final
reviewer: root/high-capability agent.
