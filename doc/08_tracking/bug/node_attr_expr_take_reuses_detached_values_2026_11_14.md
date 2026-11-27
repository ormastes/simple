# Detached expression attributes survive a store take

Status: implementation prepared; verification pending.
Canonical ID: `node_attr_expr_take_reuses_detached_values_2026_11_14`.

Source review of release `9a1efcc9940513b63fb7140483a4d5d27a1d9449`
found that `expr_store_state_take()` captures dense `extra`/`s_val` values,
then resets expression arrays and count without replacing the active detached
attribute stores. With `column` or `sparse_hash` placement, fresh allocation
reuses node IDs and can observe the previous owner's values. The default direct
placement is unaffected. This violates the take/install contract used by
ParseContext; it is independent of the visibility feature drafts.

The six-line correction calls the existing `expr_extra_load([])` and
`expr_s_val_load([])` after snapshot capture and count reset. Those helpers
replace detached stores while preserving the selected placement. The captured
snapshot owns independent dense arrays, so the reset does not erase its data.
There is no wire-layout, default-placement or visibility-policy change.

The regression in `expr_store_state_take_install_spec.spl` uses real owner
constructors and accessors. It covers direct, column and sparse-hash placement,
immediate empty presence after take, fresh allocations reusing old IDs, and
restoration of two independent snapshots. This full-import SSpec has not run.

## Bounded native projection evidence

The focused fixture copies actual production blocks from `_AstExpr/nodes.spl`
and `attribute_schema_v1.spl` without rewriting them. Per-block line ranges and
SHA256 provenance are retained in the isolated worktree under
`build/node-attr-take-projection/`. Its test-owned dense input records exercise
real install/take, fresh detached-store presence and saved values across
interleaved installs. It does not execute the parser or `expr_alloc` and is not
full-import, Phase 3 or release qualification.

Producer SHA256:
`855f48d3c9f9d915be2c8d732d4da3186caa0fb49f55ba3c780a47a1bb7efd42`.
Each case uses a tracked private Git source root, `native-build --source src
--entry src/main.spl --entry-closure --runtime-bundle core-c --threads 1`,
explicit private cache/output, a 30-second deadline and actual descendant RSS
limit of 256 MiB. No address-space limit or fabricated worker estimates.

1. Original-source RED build: 3.735 seconds, peak 187,338,752 bytes, exit 1.
2. Corrected-source GREEN build: 3.537 seconds, peak 221,433,856 bytes, exit 1.

Both stopped in MIR with the same five trait-dispatch errors: missing native
implementation for `AttrOwnerV1` with an empty receiver, and missing object-safe
`owner_read`/`owner_write` methods. Neither produced an executable, so these
are not runtime RED/GREEN evidence for the fix. The initial fixture omitted
concrete owner implementations because the exercised stores were detached.

One corrected GREEN fixture adds the existing real `OwnerCellsV1` i64 test
implementation and a genuine array-backed text receiver, both exercised by
the fixture. All 67 provenance blocks remain unchanged. Attempt 3 exited 1
after 3.087 seconds with peak tree RSS 159,232,000 bytes, before execution:
HIR rejected both implementations with `AttrOwnerV1 expects 1 type arguments,
got 0`. No resource cap fired. The exact corrected source SHA256 is
`5e897efb596fc728483dff9097c8250f3850eccb447a933343ce9612464a6a55`.

This projection route is stopped after three attempts. The conditional fourth
original-source control was not run because corrected GREEN never executed.
The production trait dispatch/implementation admission limitation remains;
there is no runtime RED/GREEN proof. Independent source review accepts the
six-line fix and the real-owner regression, but full-import SSpec execution
and runtime qualification remain pending. No parser or cache qualification
is claimed.
