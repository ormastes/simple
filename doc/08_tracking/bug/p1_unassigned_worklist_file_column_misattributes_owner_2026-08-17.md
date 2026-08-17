# The `p1_unassigned.tsv` `file` column names the wrapper, not the implementation

Date: 2026-08-17. Affects the 121-row unassigned-P1 worklist
(`scratchpad/triage/p1_unassigned.tsv`).

## Symptom

The TSV's column 5 (`file`) is used to assign rows to lanes and to check them
against the claimed-path list. For several rows it names a module that does not
contain the defect and, worse, sits in a DIFFERENT ownership zone than the code
that does. A lane filtering only on column 5 will pick up rows that belong to a
live session and edit files it was told not to touch.

Measured by following each spec's `use` lines to the real implementing module.

| doc | column-5 `file` | real implementation | verdict |
|---|---|---|---|
| `aes128_ccm_rfc3610_kat_mismatch_2026-07-20` | `src/lib/common/aes/modes.spl` | `src/os/crypto/aes128_ccm.spl` | **CLAIMED** (`src/os/crypto/**`). `modes.spl` contains no CCM at all — only CTR and CBC. |
| `aes256_ctr_keystream_wrong_after_first_block_2026-07-20` | `src/lib/common/aes/modes.spl` | `src/lib/common/crypto/aes_gcm.spl` (`aes256_key_expansion`, `aes256_encrypt_block`) | **CLAIMED** (`src/lib/common/crypto/**`). The doc's own hypothesis is an AES-256 key-schedule defect, and the CTR wrapper in `modes.spl` is proven correct by the AES-128 vectors passing through identical code. |
| `ecc_p384_p521_sign_verify_broken_2026-07-20` | `src/lib/nogc_sync_mut/io/signature_sffi.spl` | `src/os/crypto/ecdsa_p384.spl`, `ecdsa_p521.spl` | **CLAIMED** (`src/os/crypto/**`). |
| `symbolkind_enum_match_fails_cross_module_discriminant_minus_one_2026-07-29` | `src/lib/gc_async_mut/gpu/browser_engine/gpu_web/layout/contracts.spl` | `compiler.hir.hir_lowering.{types,items}` | **CLAIMED** (`src/compiler/20.hir/hir_lowering/**`, a stage-3 blocker). |

## Fix for consumers of the worklist

Derive ownership from the spec's imports, not from column 5:

```sh
grep -h '^use ' "$spec" | sed 's/^use //' | cut -d. -f1-4
```

Map `os.crypto.*` -> `src/os/crypto/**` and `std.common.crypto.*` ->
`src/lib/common/crypto/**` before claiming a row. Four of the ~21 spec-bearing
`src/lib` rows change owner under this test — roughly one in five.

## Related, and worth a re-check by whoever owns it

`interp_u64_high_bit_option_unwrap_corruption_2026-07-11` (column 5
`src/lib/common/ui/window_scene.spl`) is very likely **already fixed**. Its root
cause is `fn unsigned_ordering` in
`src/compiler_rust/compiler/src/interpreter/expr/ops.rs`, which is present in
`HEAD` — a working-copy rewind that deleted it was refused earlier today and the
function restored (see
`dirty_worktree_triage_1525_files_2026-08-17.md`).

**Do not classify this row with the deployed binary.** `bin/simple` resolves to
`bin/release/x86_64-unknown-linux-gnu/simple`, 59,536,728 bytes, mtime
2026-08-16 22:59:37 — it predates the fix and will reproduce the bug from a
stale binary, yielding a false RED. A `.spl` source change needs no build, but
this fix is in the Rust seed and does.
