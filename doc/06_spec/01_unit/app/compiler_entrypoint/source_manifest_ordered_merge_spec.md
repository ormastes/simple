# Ordered source manifest batch membership

Executable owner: `test/01_unit/app/compiler_entrypoint/source_manifest_ordered_merge_spec.spl`.

REQ-MEMBERSHIP-ORDERED-001: Preserve exact subset membership while avoiding a checkout-sized rendered-row dictionary for canonically ordered batch inputs. The source helper proves strictly increasing, delimiter-free inventory identities and nondecreasing selected identities before entering the merge. Each selected row still compares its complete identity, content digest and byte count; duplicate selected rows remain permitted. Tiny-selection binary behavior and unordered/duplicate/delimiter caller fallback remain unchanged.

| Scenario | Actual assertion |
|---|---|
| Sparse 33-row selection from 1024 ordered entries | Ordered route and full membership succeed at both inventory endpoints; caller arrays remain unchanged |
| Digest and byte-count drift | Full membership rejects each changed row independently |
| Missing identities | Reject identities before, between and after the admitted inventory |
| Repeated selection | Accept identical repeated rows, reject conflicting data for the same identity |
| Unordered selection and duplicate inventory identity | Ordered route is unavailable; original exact membership still succeeds |
| Synthetic delimiter identity and malformed row | Preserve delimiter membership through fallback; reject malformed row |

Static complexity: eligibility scans N inventory entries and M selected rows once. The merge advances its inventory position at most N times and visits M rows; it renders full rows only for compared selected matches. Auxiliary state is indices and the current identity, rather than N rendered rows and dictionary entries. This is an O(N+M) source-level comparison bound; it does not establish measured speed, RSS, compiler admission, or that membership caused the prior grouped-build timeout. Canonical inventory selection/copy/hash, manifest digest/count, owner/generation validation and publication remain unchanged.

Verification status: six executable cases prepared, but not run. The actual imported-owner native fixture has fifteen criteria, including explicit ordered/fallback eligibility. A pure `b5809193` positional diagnostic build reached runtime compilation and timed out at its 180-second bound (exit 124, peak aggregate RSS 2,548,100 KiB); no executable was produced and no runtime criteria ran. Its source pins remained unchanged, and its job was reaped with zero active descendants. Evidence: `C:/dev/simple/build/phase3-grouped-candidate-plan-20261011/focused-merge-compile1/RESULT.json`. Both environment audits and the executable-spec layout check passed. Full core/MCP/LSP checks, paired performance measurements, Phase 3, Hello World and real imported regression admission remain pending.

The two bounded cache follow-ups are also failures: attempt 2 linked an executable but returned exit 1 when no-op receipt publication failed under the long private HOME; attempt 3 used a shorter HOME and raised access violation `3221225477` during entry MIR lowering. Neither executable regression criteria nor BDD examples ran. All three jobs are terminal with zero active descendants; source pins stayed unchanged and cache/logs were preserved. See `doc/08_tracking/bug/source_manifest_batch_allocation_2026-10-11.md` for the exact evidence and remaining boundaries. No fourth focused attempt was dispatched.
