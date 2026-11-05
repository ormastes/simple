# TUI builtin len resolution fails in native closure

Status: OPEN. Workaround qualification pending.

Producer `4cca9585fbc6069e1755c9958df3fcdf05d6168046f7934f8130640f1dd23d3d`, source `902348160a80fe272ee253409f01191d830e4849`: normal CS closure HIR reports unresolved `len` in canonical TUI widget/input owners. Receipt: `/home/ormastes/simple-phase4-web-a0-parallel-20261010/cs-4cca12-epoch03/build/failure-summary.json`.

Tagged workaround spells the same text/array byte or element length with its receiver `.len()`; input codepoint cursor helpers stay unchanged. It adds no TLS dependency or host access. Safe global `len` grammar must be repaired in the compiler; this source workaround is not recovery evidence. Tests and changed closure remain UNEXECUTED.

Production workaround and native regressions: commit `02c42fc51` (qualification pending).

**Revalidated 2026-11-02: still plausible because OPEN. Workaround qualification pending; no merged fix commit with a passing regression is cited in this doc.**

**Triage 2026-11-03 (group C):** root fix landed: `8446b390c3d` adds `len` to `is_interp_builtin_fn` (HIR free-function len); pinned by `test/01_unit/compiler/50.mir/free_len_call_lowering_spec.spl`. Status: fix-implemented-verification-pending; retire tagged workaround after stage3 rebuild.

## 2026-11-05 reopen triage (verify-sweep s3_fable43 sha256 615859c5c2815f71; seed oracle bin/simple.exe sha256 8c7341592f4d47de)
Seed run of probe hir_free_len_call prints FAIL free_len, but the seed does not run the HIR fix 8446b390c3d (len in is_interp_builtin_fn); that fix is pure-Simple. The sweep's native crash (rc=-1073741819, 'rejected invalid array handle' in make_input_widget_with_value/input_delete_back) is a different, later-stage fault than the unresolved-len diagnostic and indicates an array-handle bug in native lowering of the TUI owners, not the HIR resolution. Next step: native-build hir_free_len_call.spl on a stage3 with 8446b390c3d (expect PASS free_len), then bisect the TUI crash separately with a minimal input_delete_back fixture; keep the tagged len workaround until both pass.
