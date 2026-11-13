# TUI builtin len resolution fails in native closure

Status: FIXED (closed 2026-11-13). Root fix `8446b390c3d`; native stage3 PASS 2026-11-07; regression spec green on release/1.0.0 2026-11-13. See Closure below.

Producer `4cca9585fbc6069e1755c9958df3fcdf05d6168046f7934f8130640f1dd23d3d`, source `902348160a80fe272ee253409f01191d830e4849`: normal CS closure HIR reports unresolved `len` in canonical TUI widget/input owners. Receipt: `/home/ormastes/simple-phase4-web-a0-parallel-20261010/cs-4cca12-epoch03/build/failure-summary.json`.

Tagged workaround spells the same text/array byte or element length with its receiver `.len()`; input codepoint cursor helpers stay unchanged. It adds no TLS dependency or host access. Safe global `len` grammar must be repaired in the compiler; this source workaround is not recovery evidence. Tests and changed closure remain UNEXECUTED.

Production workaround and native regressions: commit `02c42fc51` (qualification pending).

**Revalidated 2026-11-02: still plausible because OPEN. Workaround qualification pending; no merged fix commit with a passing regression is cited in this doc.**

**Triage 2026-11-03 (group C):** root fix landed: `8446b390c3d` adds `len` to `is_interp_builtin_fn` (HIR free-function len); pinned by `test/01_unit/compiler/50.mir/free_len_call_lowering_spec.spl`. Status: fix-implemented-verification-pending; retire tagged workaround after stage3 rebuild.

## Verification

Verified natively on stage3 s3_fable57s (2026-11-07): RESULT rc=0 PASS

## Closure 2026-11-13 (UI batch B, Linux aarch64, release/1.0.0 @ 35144b7f5e93)

Closed as fixed on three pieces of evidence:

1. Root fix `8446b390c3d` is an ancestor of release/1.0.0: `len` is
   allow-listed in `is_interp_builtin_fn`
   (`src/compiler/20.hir/hir_lowering/_Expressions/expression_support.spl:57`)
   and MIR re-dispatches the bare call.
2. Its pin `test/01_unit/compiler/50.mir/free_len_call_lowering_spec.spl`
   re-run today on the Rust seed: `SPEC FILE VERDICT ... outcome=OK
   declared>=1 executed=1 passed=1 failed=0`, rc=0.
3. The native requalification this record waited for: investigation-log row
   995, native stage3 `s3_fable57s`, fixture
   `test/fixtures/lib/tui_len_receiver_workaround/main.spl`, rc=0 PASS
   (2026-11-07). That supersedes the 2026-11-05 `s3_fable43` crash row.

### Separate defect seen while re-running the fixture (not `len` resolution)

On this host's seed (`simple-seed-v4`, v1.0.0-rc.1) the same fixture exits
**rc=3**, in both `SIMPLE_EXECUTION_MODE=jit` and `=interpreter`. The JIT run
printed no `[engine-demotion]` or fallback line and no unresolved-name
diagnostic, so `len` resolved; the failure is the value check
`input_delete_back(...).value != "é"`.

Cause, measured with a three-line probe on the same seed: `"é🙂".substring(0,
2)` returns `é🙂`, and `.substring(2, 6)` returns the empty string. This seed
slices by CODE POINT (the #7877 switch, see
`text_len_codepoint_switch_2026-11-03.md`), while
`src/lib/nogc_sync_mut/tui/widgets/input.spl` correctly passes BYTE offsets
bounded by `byte_len()`, which is the documented contract and the 2026-11-13
owner decision. `input.spl` was not changed: it is right, and the seed is what
moves (seed commit `a3dfd43c52e`, branch `work/seed-text-byte-slice-20261112`,
not yet on release/1.0.0). Re-run this fixture on the first seed that carries
that commit; it should print `tui-len-receiver-ok`.

Follow-up kept from the 2026-11-03 triage: retire the tagged receiver `.len()`
workaround in the TUI owners once a stage3 rebuild is deployed.
