# TUI builtin len resolution fails in native closure

Status: OPEN. Workaround qualification pending.

Producer `4cca9585fbc6069e1755c9958df3fcdf05d6168046f7934f8130640f1dd23d3d`, source `902348160a80fe272ee253409f01191d830e4849`: normal CS closure HIR reports unresolved `len` in canonical TUI widget/input owners. Receipt: `/home/ormastes/simple-phase4-web-a0-parallel-20261010/cs-4cca12-epoch03/build/failure-summary.json`.

Tagged workaround spells the same text/array byte or element length with its receiver `.len()`; input codepoint cursor helpers stay unchanged. It adds no TLS dependency or host access. Safe global `len` grammar must be repaired in the compiler; this source workaround is not recovery evidence. Tests and changed closure remain UNEXECUTED.

Production workaround and native regressions: commit `02c42fc51` (qualification pending).

**Revalidated 2026-11-02: still plausible because OPEN. Workaround qualification pending; no merged fix commit with a passing regression is cited in this doc.**

**Triage 2026-11-03 (group C):** root fix landed: `8446b390c3d` adds `len` to `is_interp_builtin_fn` (HIR free-function len); pinned by `test/01_unit/compiler/50.mir/free_len_call_lowering_spec.spl`. Status: fix-implemented-verification-pending; retire tagged workaround after stage3 rebuild.
