# Protected Simple Release Skill

Follow `doc/07_guide/infra/software_release.md`. The canonical version is `release/version.sdn`; other locations are projections.

Require verified SPipe/manual evidence and one release-bound `bin/simple test test --whole --mode=interpreter` PASS. Work only in one isolated release session with a unique branch and worktree. Beta work targets `release/X.Y` and admits only explicit reviewed bug-fix backports with exact stable patch-ID equivalence, provider-bound review/check receipts, and renewed result-revision evidence. Adapted patches fail closed until a separately reviewed equivalence protocol exists.

Before each candidate attempt, after a bootstrap failure fix, and before release admission, fetch once and compare exact `main` and release-line snapshots read-only. Discovery only proposes reviewed fixes. Backport a selected trunk fix or forward-port a shared release-first fix through its own isolated work branch before candidate admission, with renewed evidence, a divergence receipt, and protected CAS integration. Only a `non_fix` release-specific compatibility classification with reason, owner, and expiry may remain release-only. Keep `main` as development trunk: never reset/repoint it to, track, or replace it with `release/X.Y`.

Create an immutable candidate before builds. Build once, admit exact digests, then perform promotion without rebuilding through one signed annotated exact tag. Ask before external push/publication.

Never author in the main worktree, directly update protected refs, automatically select fixes, make broad tag pushes, delete/move/reuse published tags, or accept fallback artifacts. Rollback redeploys an earlier admitted release; withdrawal preserves published identity; corrections use a new beta/RC/patch identity.

Validation commands: `simple release version-check`, `beta-prepare`, `backport-check`, `candidate-check`, `promote-check`, and `withdraw-check`.

GitHub forbids PR authors from submitting an `APPROVED` review on their own PR. Protected integration uses the required `SPipe Self Review Admission` status instead; it is not provider or independent approval. Explicit `self_attested` high-capability/high-effort PASS with zero P0/P1 binds protected target/ruleset, head, base, merge-base, and diff for ten minutes. Ordinary code/text is default allow absent operator deny/constrain through `code`, `text`, exact `file`, immediate `directory_files`, and recursive `directory_recursive` scopes. On rejection/invalidation, follow the reason: drift/expiry needs fresh exact-head review+dispatch; deny needs external policy-owner action or an eligible independent route; uncovered scope needs a smaller diff/new constraint; unsafe or secret material must be removed and credentials rotated. Never attempt author `APPROVED`, reuse a stale check, or weaken candidate/release/publication authority. Generic Actions App trust risk is user-accepted, not independent security. Release-environment approval and candidate admission remain separate.

Live rulesets, signing, protected pushes, and publication require explicit authority. A local plan PASS is not live release evidence.
