# SimpleOS Toolchain Self-Host Bootstrap — TLDR

Full plan: `toolchain_selfhost_bootstrap_plan.md` (2026-08-06).

- Arch: **x86_64 primary** (OVMF proxy + KVM + proven clang ladder), riscv64
  secondary (OpenSBI, serial-only), aarch64 deferred (filed EFI-stub gap).
- Fork already exists: `github.com/ormastes/llvm-project` branch `simpleos`;
  lane F1 = pin bump `3b33ba807`→`92fa40246` + push/parity check.
- Nothing prebuilt survives today: cross clang/lld, `clang_static`, and both
  `bin/release/*-unknown-simpleos/` payloads are ABSENT — rebuild lanes C1/S1
  start first (C1 is the multi-hour long pole).
- G2 exit = in-guest compile (`-cc1`) + in-guest link (`lld_static`, ladder
  rungs 3–6, authored never run) + FS-exec run printing hello on the SimpleOS
  terminal.
- Clang self-bootstrap staged honestly: B1 single-TU witness (preprocessed `.i`
  dodges FAT32 root-only/8.3 + no-fork), B2 FAT32 subdirs, B3 fork/exec on the
  FS-exec path, B4 full self-build (long-horizon, ≥8 GB RAM gate).
- G4: P1 `simple --emit-object` + in-guest lld link + run; P2 self-host staged
  behind D2/D3 fixes and B2.
- Defect gates: D1 deployed-selfhost SEGV (build payloads with the bootstrap
  seed), D2 #99 enum miscompile, D3 freestanding landmines, D4 stale toolchain
  guide (fix in C2).

```sdn
graph: {
  t0_parallel: [C1_llvm_build, S1_payload, F1_fork_pin, C2_doc_fix, B2_fat32_subdir, B3_forkexec]
  C3_cc1_rerun: [C1_llvm_build]
  C4_inguest_link: [C3_cc1_rerun]
  S2_install_image_gate: [S1_payload]
  B1_selfcompile_witness: [C3_cc1_rerun]
  P1_simple_emit_obj_run: [S2_install_image_gate, C4_inguest_link]
  B4_full_clang_selfbuild: [B1_selfcompile_witness, B2_fat32_subdir, B3_forkexec, C4_inguest_link]
  P2_simple_selfhost: [P1_simple_emit_obj_run]
}
```
