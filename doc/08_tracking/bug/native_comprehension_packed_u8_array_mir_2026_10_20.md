# Self-hosted MIR rejects a list comprehension over a packed [u8] array

- Canonical id: native_comprehension_packed_u8_array_mir_2026_10_20
- Date: 2026-10-20
- Status: open (workaround active)
- Producer: producer4 strict (`simple-producer4-strict.exe`, source 02ca146 + 81e50f5d441),
  phase-3 native-build of `src/app/cli/bootstrap_main.spl`, x86_64-pc-windows-msvc, llvm.
- Original failure: `E-MIR-EXPR-Comprehension: unsupported in stage2: comprehension over a
  packed [u8]/[u64] array (its slots are raw, not tagged); index it in a while loop` at
  `src/compiler/10.frontend/frontend_advisory_preprocess_port_v1.spl:90`
  (`sha256_bytes([value as i64 for value in text_to_bytes(source)])`). The Rust seed compiles
  the same source.
- Workaround: the comprehension is rewritten as a counted `while` loop that widens each byte
  to i64, marked `# @workaround bug=native_comprehension_packed_u8_array_mir_2026_10_20`.
  Recovery reference for the original form: `35123ed70c0`.
- Root fix needed: comprehension lowering in `src/compiler/50.mir` must read packed byte/u64
  slots raw (as the indexed for-in path already does) instead of rejecting them.
- Retirement: restore the comprehension once the root fix lands and a rebuilt producer lowers
  the original form.
- DB reconciliation: pending (no qualified `check-dbs` CLI on this host).
