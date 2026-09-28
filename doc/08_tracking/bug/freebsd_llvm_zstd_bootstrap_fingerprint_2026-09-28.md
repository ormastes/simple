# FreeBSD LLVM zstd fingerprint failure

## Observed failure

The canonical FreeBSD x86_64 QEMU `--full` run reached Stage 2, then stopped with `error: failed to fingerprint Rust seed inputs`. The retained guest manifest recorded `phase=pre`, `status=1`; its stderr log contained only `phase=pre`. The failed guest overlay is retained locally at `build/freebsd/vm/failed-stage2.overlay.qcow2`.

## Cause and fix

An isolated guest run of `bootstrap_stage3_resolve_llvm_build_authority` stopped at `llvm-system-lib-0006-token=-lzstd`. FreeBSD's zstd package puts `libzstd.so` in `/usr/local/lib`; the helper searched the LLVM libdir and `cc -print-file-name`, which returned an unresolved library name. Commit `8f78397c073ecc1d48af5d1326f9f0f57dac099e` includes `/usr/local/lib` in the FreeBSD system library search path while retaining canonical path and SHA-256 binding.

## Verification

- In the retained VM with only the patched authority file copied, the LLVM authority helper passed and bound `/usr/local/lib/libzstd.so.1.5.7` and its SHA-256.
- The complete Rust seed fingerprint helper then passed with hash `d4a5536e284b237c979fa03b69c6231c062551e087f6751b3172921771b900f4`.
- The canonical `--full` retry from source base `d86255637d31befe6cee52f6be25f32974d559fb` plus commits `48d7f560da2892579b6fb3a77b123de4a624804f` and `8f78397c073ecc1d48af5d1326f9f0f57dac099e` passed this fingerprint gate and reached Rust seed compilation. It then exposed a separate missing header in the VM sync, recorded in `freebsd_qemu_arm_host_tcg_preflight_2026-09-28.md`. Its stdout is retained at `build/freebsd/qemu-run-logs/freebsd-qemu-full-retry.log`.
- The final canonical `--full` run, also including header-sync commit `6771f129572d889422ee38b2b3fbf58fb6172d5b`, passed fingerprinting and Rust seed compilation. It expired at the configured two-hour Stage 2 SSH timeout while the native Rust build was still active. The exact terminal result and local log hashes are recorded in `freebsd_qemu_arm_host_tcg_preflight_2026-09-28.md`; this run does not qualify the full bootstrap or a later source head.
