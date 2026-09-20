
## 2026-09-17 full unit-sweep (macOS arm64, seed v1.0.1-beta.1, parallel 13-lane xargs run)

Totals across chunks: PASS≈2760 FAIL≈850 (rate ~23%, consistent with repo's honestly-RED advisory state). Chunks: common 837P/263F(+12 timeouts under bootstrap load), gc_async_mut 315P/123F, nogc_async_mut 310P/45F, nogc_sync_mut 212P/47F, gpu 74P/39F, e-p group 171P/52F, a-d group 51P/26F, skia/ui group 130P/47F, db group 88P/65F, extended/crypto/std 158P/48F, s-z+rest 134P/61F, engine group 109P/29F, tools 45P/5F.

Dominant failure clusters (attribution: spec↔lib API drift + unimplemented planned modules, not this-lane regressions):
- auto_comprehensive_1..30: dict_keys free-fn absent from src/lib (30)
- MISSING_MODULE ~30: std.common.debug.{aop_aspect,wire_dispatch,wire_execute}_v1, common.ui.render_opt.*, common.wine_proton_gate, std.common.spec.*_evidence
- wine_dll_view/process_session_*: PEB/TEB/TLS layout assertions (13)
- PARSE unclosed-backtick cluster (12+9)
- singles: crypto lshr negative-shift, tls12_prf_kat bytes_to_hex recursion stack-overflow, sha3_jit_engine_divergence, base64url decode, many *_not-found API drift

Tools lane: 45/50 pass. kernel_plugin_schema x4 = one shared cause (float version rejected by _required_text). mail_cli: GNU date -d + GNU sed \+ BRE quantifier — real BSD/macOS portability bugs in tools/mail-cli/lib/format.shs:262.

Per-chunk tallies and full classified failure lists: /tmp/sweep-*.log and agent logs (this session).
