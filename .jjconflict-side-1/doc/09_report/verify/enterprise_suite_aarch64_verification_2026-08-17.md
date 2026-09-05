# Enterprise Suite — independent aarch64 verification of the 49-spec suite (2026-08-17)

- Lane: `.spipe/simple_enterprise_suite`
- Host: macOS aarch64 (this checkout), interpreter mode, one spec per process
- Purpose: an independent second-host confirmation of the lane's 49/49 claim,
  which was measured on an x86_64 Linux seed. Recorded as a report rather than
  appended to the lane state file because that file is under active concurrent
  edit by other sessions (an append raced and conflicted during this pass).

sync + independent verification (2026-08-17, original Wave A-C session,
macOS aarch64 host): fetched onto `0b88b24533f1`; confirmed the Wave A-C
landing `42508ae90fb9` is an ancestor of current origin and that http_core /
enterprise_store / enterprise_sale survived the 155 upstream commits intact.
Upstream `18bfc6b155` resolved the TE contradiction this lane recorded on
08-14 the right way: the sync TRANSPORT now rejects every non-empty
Transfer-Encoding (501) in `headers_decision`, while the shared core keeps
`allow_chunked=false` semantics for chunked specifically — transport-specific
strictness layered over the core, not a fork of it; `chunked_rejection_spec`
was updated in the same commit and is green here (15/15).

BINARY IDENTITY (this host): `bin/release/aarch64-apple-darwin/simple`,
`Simple v1.0.0-beta`, 29,315,096 bytes, mtime 2026-07-25 14:15:52,
sha256 f2c216a660da83da1a253d2e8191a3059a66b1d9dc11bbcbaf237fe7e5b8d2bc.
This is OLDER than the x86_64 Linux seed (59,536,728 B, 2026-08-16) behind
the 49/49 W10-A row, which is why the two runs disagree — see below.

SWEEP (the full 49-spec suite: 28 test/-tree + 21 ubs_test). One spec per
process, `SIMPLE_TIMEOUT_SECONDS=900`, interpreter mode, verdict read from
the `Results:` line; no run was killed and no row lacks a verdict line.
**43/49 spec files green; 449 examples executed, 440 passed, 9 failed.**
- ubs_test (the AC-14 rewired ERP example): **21/21 green, 143/143
  examples**, including `restaurant_lane_spec` 12/12 — the harness-plumbing
  row the W10-A note flagged is healthy here too.
- test/-tree: 22/28 green, 306 examples, 297 passed, 9 failed.
All 9 failed examples are attributable to TWO pre-existing, already-filed
seed defects on this older binary — none is an enterprise-code regression:
- `use app.<pkg>.main` -> `semantic: type mismatch: cannot convert dict to
  int` (5 specs x 1 example: back_office_web, enterprise_security_audit,
  enterprise_web_app, store_app, store_web_harden). Filed and explicitly
  known-incomplete:
  `doc/08_tracking/bug/chore_commit_941605d43d9_hidden_semantic_changes_2026-08-01.md`
  ("hunk B's Single/Aliased carve-out leaves `use pkg.main` still failing").
  Predicted-then-confirmed: grepping the 28 for `^use app\..*\.main` returns
  exactly those 5 files.
- typed-`u8` byte-array element -> `semantic: byte array element must be
  integer, got u8` (1 spec x 4 examples:
  `http_dynamic_dispatch_live_socket_spec`). Filed:
  `doc/08_tracking/bug/udp_send_to_rejects_typed_u8_array_2026-07-04.md`.
Classification across all 49: 43 passed / 6 binary-blocked / 0 code-failed /
0 timeouts / 0 missing-verdict. A newer binary is the resume condition for
those 6 rows on this host; they are green on the lane's Aug-16 x86_64 seed,
so this is a binary-divergence row, NOT a contradiction of the 49/49 claim.

WORKING-COPY STALENESS REPAIR (anti-clobber, forward-only). The shared WC
held a pre-hardening snapshot of this lane: `state.md` 756 lines behind,
`enterprise_store.md` 457 behind, `http_core.spl` 159 behind, `store.spl`
260 behind, `audit_hash.spl` and `file_backend.spl` ABSENT, 18 of the 28
spec files ABSENT, and `examples/12_business/simple_erp/ubs_test` still on
the pre-AC-14 in-memory `used: [text]` form. Per vcs.md both directions were
diffed before every restore: every WC-side "insertion" was strictly older
content (including the sync Router fn-field dispatch that W2-B had already
fixed), so origin was strictly ahead on every path and nothing unique was
lost. Restored forward from `main@origin`: the enterprise_* lib modules,
`src/app/enterprise{,_store_app}`, both http_server trees, `common/net`,
this lane's spec dirs, `examples/12_business/simple_erp`, the lane guides,
wiki entry and this state file. The lane surface now matches origin exactly.
NOT touched: the 52 files conflicted from other lanes' uncommitted work.
STILL OUTSTANDING AND NOT MINE TO FIX: the shared WC remains ~109,001 lines
behind origin across 1,243 files repo-wide — any whole-WC commit from any
session would revert that much landed work. This is the same hazard this
lane's own MERGE HAZARD LOG recorded on 08-16; it is now quantified and
filed repo-wide as
`doc/08_tracking/bug/shared_working_copy_109k_lines_behind_origin_2026-08-17.md`
(includes the proposed content-freshness pre-push guard, since the tree-size
guard counts files and cannot see per-file staleness).

EVIDENCE TRACEABILITY NOTE: the wiki's 49/49 row cites tip `0a12ca93433`,
and this state file cites `709ea3644cf`, `9b42402f98d`, `90e2b6e1b9b`;
none of those SHAs exists in this repo, and `a24e214200d` exists locally but
is not an ancestor of origin. The CONTENT landed (this sweep exercises it and
22/28 are green), but the citations are lane-worktree SHAs rewritten by the
3-way merges, so they cannot be resolved by a reader. Future rows should cite
the merge commit that actually landed on main.

Also stale for a reader: the `## Phase` line above still says
"implement (Wave A in progress)" while the log records work through W13-C.
Left unedited deliberately — this lane is actively driven by other sessions.
