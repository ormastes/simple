# Owned archive weave compares different source-binding domains

Status: OPEN — source correction prepared; future compiler execution and native qualification pending.

The actual strict tiny06 owned-archive transaction publishes a journal with source binding `3d1d328810c284a466b0015c28da2feb10886397f4cfc0984b62234b09c4b9fd` and a captured policy/schedule binding `e0dd1e9139b1bcb6ac38d742955bb7065e855130d934f33e1b03085683a2799d`. Journal key, registration digest/epoch and provider selection match the actual predecessors. Evidence: `/Users/ormastes/wt/release-phase2-review/build/verify/tiny06-owned-weave-binding-diagnosis-20261026-01`.

The journal hashes `driver-hir-journal-sources-v1` with its five source fields. The actual streaming schedule hashes `driver-hir-schedule-source-v1` with nine fields. Their digests intentionally represent different contracts. Policy v1 captures and encodes the schedule source binding alongside the schedule digest and journal key. Comparing its source binding to the journal digest rejects genuine publication.

The correction compares policy source binding with the actual schedule source binding. Before this comparison, the production entrypoint replays the actual schedule against the driver's retained source/surface owner and verifies the actual journal against the retained source owner, registration and immutable event chain. Each event's key binds the journal-domain source digest. The policy journal-key comparison, schedule digest, registration, selection, source custody and cache checks remain unchanged. No codec version change is needed: the v1 policy field retains its original schedule-domain meaning.

The genuine native boundary fixture now calls production input admission after the real selected source-to-HIR transaction and policy capture. It asserts distinct digest domains and accepts the genuine pair, then independently mutates/restores journal source binding, schedule source binding, policy source binding, policy journal key and policy schedule digest. Each negative must refuse and each restored owner must admit.

Validation: source review and `git diff --check` only. The new controls have not executed. Existing retained P2 has immutable old code and cannot benefit from this source fix. Strict tiny06 remains terminal; do not retry it, rewrite its journal/policy, fabricate equality or bypass validation. No P2, runtime, Rust or compiler rebuild was performed. Native qualification and full P3 remain OPEN.
