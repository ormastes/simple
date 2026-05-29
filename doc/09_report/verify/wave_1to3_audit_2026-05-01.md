# Wave 1–3 Audit — 2026-05-01

Status: AUDIT (process evidence, not artifact verification)
Scope: 24 parallel Opus+advisor agents executed across compression / cipher / SIMD plan trees on 2026-05-01.
Author: T25 (Wave-4 cleanup sweep, doc-only)

This report captures (a) commits whose `jj describe` titles do not match their tree contents because of jj parallel-reconcile bundling, (b) recovery actions taken by individual agents, (c) bug-doc framings that were disproved on contact, and (d) reusable process patterns surfaced by the wave. It is *evidence*, not narrative — neighbors in `doc/09_report/verify/` (e.g. `simd_phase2_evidence_2026-05-02.md`, `rtl_mdsoc_baseline_2026-05-02.md`) follow the same shape.

## Summary

- 24 parallel agents (Opus orchestrator + advisor each).
- ~60 commits landed on `main` (HEAD `voqupwqqwzxt` at audit time).
- 12 bug docs filed today under `doc/08_tracking/bug/*_2026-05-01.md` (verified count; the wave kickoff brief said 10).
- 5 feature requests filed today under `doc/08_tracking/feature_request/*_2026-05-01.md` (verified count).
- All 3 plan trees (compression, cipher/crypto-recovery, SIMD) advanced.

## Mislabeled commits

Verified against `jj show --summary` and `git show --name-only` against HEAD `voqupwqqwzxt` at audit time. "Title" = `description.first_line()`; "Actual content" = files surfaced in the summary.

| jj change-id | git short-sha | Title | Actual content (verified) | Reported by | Recovery status |
|---|---|---|---|---|---|
| `kkuvwnzllopq` | `82978373e4` | feat(sha256): vectorize message schedule using simd_int_ops Phase 1 | sha256 scalar parity helper only — title overstates scope; the bulk vectorization diff is bundled into `zkxuxttwpzpw` (see next row) | T2 | Tree-content correct; title misleading. Defer rename to a quiescent session. |
| `zkxuxttwpzpw` | `7c32d2eeff` | test(pbkdf2): RFC PBKDF2-HMAC-SHA-512 industry vectors | Bundled — pbkdf2 vectors **plus** `doc/06_spec/app/compiler/feature/portable_simd_fp_modules_spec.md`, riscv_fpga_linux design tree, rtl_riscv_mdsoc_capsules, `simd_int_intrinsics_for_crypto_2026-05-01.md`. The sha256 SIMD diff and the SIMD parity spec ride here. | T2 | Tree-content correct; title misrepresents scope. Defer rename. |
| (n/a) | `3a4af02692` | feat(os/riscv): canonical HalSmp/HalCache trait method wrappers — AC-1/AC-2/AC-3 | Two-file commit: `simd_int_intrinsics_for_crypto_2026-05-01.md` (FR cross-link) + `src/os/crypto/ecdh_p256.spl`. **Zero HalSmp/HalCache content.** | (cross-confirmed by T2 & T7) | Tree-content present (FR cross-link, ecdh_p256). The HalSmp implementation actually landed in change `pkrosyyskmsn` later. Defer rename. |
| `zkxuxttwpzpw` (same as above) | `2487c706a0` | (per brief — git short-sha `2487c706a0` resolves to the zk change above; git's HEAD-ordering and jj's order diverge under reconcile) | 74 files changed, 5698 insertions(+) — bundled output of multiple agents (chacha20.spl, sha256.spl, ecdh_p256.spl, riscv_fpga_linux design tree, hardware FPGA scripts, rtl_linux status, plus the SIMD plan spec and FR doc). Brief reported 73; verified 74. | T1 | Tree-content correct; title is severely under-representative. Defer rename. |
| `zmtlnurzsusm` | `e9c433040c` | feat(tls13): HelloRetryRequest detection + ClientHello2 construction (RFC 8446 §4.1.4) | `src/os/tls13/handshake13.spl` + 2 lzma_tiny_dbg specs. **No `ed25519` files at audit time.** | G (reported absorption of fix-commit) | The `fix(ed25519)` commit is now its own change `slskomnpwpsr 61919968d79a` ("constant-time scalar multiplication on secret path"). G's report appears to describe a transient reconcile state that subsequently corrected itself; the durable HEAD has the ed25519 fix as a separate commit. **No further recovery needed.** |

### T7 squash (`jj squash --from <kt|zk> --to @`) — partial recovery

T7 reported that `ecdh_p256.spl` had been auto-snapshotted into `kt` (riscv-hal) and `zk` (pbkdf2-vectors), and used `jj squash --from <them> --to @` to extract the file. Verified at audit time:

- `ktptyxlqnkot` (kt) post-squash contains exactly **one file**: `M doc/08_tracking/feature_request/simd_int_intrinsics_for_crypto_2026-05-01.md`. The HalSmp/HalCache implementation that the title claims is **not** present here — it landed via change `pkrosyyskmsn 178aeab` (`feat(os/riscv): real HalSmp/HalCache/DTB/CMO/per-CPU production modules`). kt's title and content disagree, but kt is durable as a tiny doc-only commit; T7's extract did not over-strip.
- `zkxuxttwpzpw` (zk) still carries 30+ files including the riscv_fpga_linux design tree, `portable_simd_fp_modules_spec.md`, and the SIMD FR doc — i.e. the squash pulled `ecdh_p256.spl` out of zk but did not undo the broader bundle. zk's pbkdf2 vectors are durable.

**Net recovery**: the ecdh_p256.spl file content is durable on HEAD (via `xqxspqnmyyqk feat(crypto): P-256 ECDH ephemeral keypair gen`); kt/zk titles remain misleading but their tree contents are non-destructive (FR cross-link, doc tree, test file). No source-code recovery is required.

## Bundle/extraction recoveries — durability check

Independent of commit-title accuracy, the following agent-claimed artifacts were verified durable on HEAD at audit time:

- T7 P-256 ECDH ephemeral keypair: `xqxspqnmyyqk feat(crypto): P-256 ECDH ephemeral keypair gen`, plus `vovnmzmknppp feat(tls13): secp256r1 NamedGroup advertise + dual key_share`, plus `onllvytpzmkt test(tls13): P-256 NamedGroup format + ephemeral keypair smoke`, plus `voqupwqqwzxt doc(tls13): cross-link P-256 NamedGroup landed`.
- G ed25519 CT fix: `slskomnpwpsr fix(ed25519): constant-time scalar multiplication on secret path`, plus `moyxmwpopoql test(ed25519): CT property spec for scalar_mul`, plus `pxyzmrkpozrr doc(ed25519): mark scalar_mul CT bug FIXED`.
- I HRR + EncryptedExtensions: `zmtlnurzsusm`, `wuxlnotwnsus`, `qqlspvtmomsp`, `lnrykmuxpvwz`, `tommnsylmyvw`, `uvunwurosuqv`.
- T2 SHA-256 SIMD parity: spec under `test/unit/lib/crypto/sha256_simd_parity_spec.spl` reachable from zk's bundled tree.
- T1 ChaCha20 SIMD parity + bench: `chacha20_simd_parity_spec`, `chacha20_simd_bench_spec` reachable from `2487c706a0` bundle.
- HKDF: `utwkxrxlrkrs`, `msvzyqxuvmqt`, `mwnzlmronkxy`, `nvxzzsymluns`.
- Zstd dictionary frame: `pxynllsspsnm`, `lwsouuklnnqm`, `nzwsktltpknr`.

Conclusion: the on-disk artifacts are durable even where commit titles mislead. Title rewrites are *cosmetic* and best deferred.

## Bug-doc framings disproved (verified count: 7 of 24 ≈ 29 %)

Each entry: filer-agent → original framing → real cause as established by today's investigation.

- **G** — `ed25519_rfc8032_vector_mismatch_2026-05-01` initially framed as a byte-mismatch in `point_compress`; real cause turned out to be a constant-time scalar-mul leak — fix landed in `slskomnpwpsr`, vector mismatch was a downstream symptom (cross-linked in `oqpquwmyszmu`).
- **Q** — `aes128_gcm_stub_2026-05-01` framed as missing `rt_aes128_gcm_*` externs; real cause was that the externs existed but were not in the FFI dispatch table — fixed by `yotnyuxtuoyw feat(interp): wire 4 AES externs into interpreter dispatch + FFI table`. Marked FIXED in `qmooqrtsumru`.
- **T8** — `interpreter_match_ok_arm_text_type_lookup_2026-05-01` framed as a `match` arm issue; real cause was helper-fn-return-from-match resolved correctly under interpreter (regression-guarded by `oxumorrkmzqs`); the bug doc was closed as INVALID by `rszsowvlowpt doc(interpreter): close 'helper-fn return-from-match' Future-work item — INVALID`.
- **T16** — `interpreter_u32_wrap_subtraction_2026-05-01` filed against the LZMA range-coder lane; surfaced as a real interpreter limitation but not the actual blocker for that lane.
- **T3** — `aes128_gcm_decrypt_string_to_int_2026-05-01` framed as a string→int parsing bug; real cause was leftover `_debug_bytes` scaffolding tripping a semantic check — fixed by `kwnportwwksr fix(aes-gcm): drop leftover _debug_bytes scaffolding`. Marked FIXED in `rponkqvrvnvl`.
- **T5 / `hmac_sha512_pbkdf2_mismatch_2026-05-01`** — framed as an HMAC-SHA-512 PBKDF2 mismatch; real cause was the bug-doc had compared `'passwd'` impl output against an RFC vector for `'password'` (per zk commit description, this is bug-doc author error, not impl). Industry vectors PASS (`zkxuxttwpzpw test(pbkdf2): RFC PBKDF2-HMAC-SHA-512 industry vectors`).
- **T1** — surfaced (not filed) the Phase-1 `rt_simd_add_i32x4` dispatch gap: declared as extern in `simd.spl` but no interpreter dispatch arm exists. Worked around in T1's ChaCha20 vectorization with direct field arithmetic; T20 is backfilling now.

## Process patterns observed (4)

1. **Parallel-reconcile bundles when 5+ agents share file-cluster.** When ≥5 agents have working-copy edits in the same directory tree (e.g. `doc/02_requirements/feature/riscv_fpga_linux*`), jj's auto-snapshot reconciles inflight edits into whichever change is currently active in the parallel-claude that next runs `jj describe` or `jj commit`. Title vs. tree-content drift is the norm under this load. Mitigation: split file-clusters across agent assignments, not just feature areas.
2. **`bin/simple test` (stale release binary) vs `bin/simple <spec>` (bootstrap binary) dispatch trap.** Multiple agents reported that `bin/simple test` returned PASS while `bin/simple test/unit/.../spec.spl` returned FAIL on the same spec. Per `feedback_compile_mode_false_greens.md`, the release binary's `--mode=native` stub-generation no-ops unresolved std calls and the `--mode=smf` swallows runtime errors. Verifying in interpreter mode via `bin/simple <spec.spl>` remains the only reliable signal until R2-broader lands.
3. **Advisor refused two fabricated commits this wave.** T11 AC-4 (claimed feature) and T5's fix-commit (claimed root-cause fix) were both rejected by the advisor when the agent could not produce primary-source evidence under prompted reconcile. The pattern (advisor as final fabrication-gate) held; both were re-routed to bug-doc filings.
4. **Vertical SIMD layout outperforms horizontal when shuffle/permute primitives are missing.** T1 ChaCha20 with vertical 4-block layout achieved 1.7–1.8× over scalar in interpreter mode for 256 B–1 KiB payloads. T2 SHA-256 message-schedule with horizontal layout was only 1–6 % slower than scalar because σ0 is the only 4-wide-parallelizable subroutine and shuffle-equivalents must be emulated via field-arithmetic. **Implication for Wave 4+**: prefer vertical layout (parallel independent message blocks) over horizontal (parallel lanes inside one block) until Phase 2 (`Vec16u8` shuffle) lands.

## Open items going into Wave 4

Surfaced by the wave but not closable in-wave:

- `rt_simd_add_i32x4` / `_sub_i32x4` / `_mul_i32x4` (and i32x8 siblings) declared as externs in `simd.spl` but **no interpreter dispatch arm**. T20 backfilling 2026-05-01 evening.
- No distinct `u32` interpreter type — wraparound semantics simulated via i64 mask. Filed as `interpreter_u32_wrap_subtraction_2026-05-01` (T16).
- TLS only advertises `TLS_AES_128_GCM_SHA256`; AES-256 cipher suite (`TLS_AES_256_GCM_SHA384`, 0x1302) missing. T21 implementing.
- P-256 scalar multiplication is **not constant-time** on the secret path. FR `p256_scalar_mult_constant_time_2026-05-01` filed.
- HRR connect-flow integration is **unblocked** by T7's P-256 NamedGroup advertise + keypair gen, but no in-wave agent owned wiring it through `tls13_client_connect`. Defer to Wave 5.
- Zstd FSE Huffman-weight Kraft completion (`bug_zstd_fse_huffman_weight_kraft_2026-05-01`) — multi-day; blocks compression M3 closure end-to-end test.

## Recovery recommendation

**Do not surgical-rewrite commit titles during a parallel storm.** Every `jj describe` operation in a colocated jj+git repo with active parallel agents triggers another reconcile and risks pulling fresh inflight edits into the rewritten commit (see `feedback_jj_uncommitted_clobbered_by_parallel.md`, `feedback_sync_bundling_clobbers_commits.md`). The title-vs-content drift documented above is **non-destructive** at the tree level — every artifact claimed by an agent is reachable on HEAD by file path. Defer commit-message rewriting to a future quiescent session via `jj rebase --skip-empty` followed by per-commit `jj describe`. Mid-wave the audit *trail* (this report) is the recovery; the commit log will catch up later.

## Appendix: change-id ↔ git-sha mapping (audit-time HEAD = `voqupwqqwzxt`)

- `kkuvwnzllopq` ↔ `82978373e4` / `d41579300f94`
- `zkxuxttwpzpw` ↔ `7c32d2eeff` / `8aea59991511` (also bundles `2487c706a0` per brief — verified one of these is a stale alias from T1's pre-squash report)
- `ktptyxlqnkot` ↔ `178aeab47467`
- `zmtlnurzsusm` ↔ `e9c433040ce6`
- `pkrosyyskmsn` (real HalSmp/HalCache impl) ↔ commit not separately resolved at audit time; cross-listed via jj log only.

Audit produced 2026-05-01 evening, T25 (Wave-4 cleanup sweep).
