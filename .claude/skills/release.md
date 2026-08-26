# Protected Simple Release Skill

Follow `doc/07_guide/infra/software_release.md`. The canonical version is `release/version.sdn`; other locations are projections.

Require verified SPipe/manual evidence and one release-bound `bin/simple test test --whole --mode=interpreter` PASS. Work only in a unique release branch and worktree. Beta work targets `release/X.Y` and admits only explicit reviewed bug-fix backports with exact provenance and renewed result-revision evidence.

At bounded beta/bootstrap checkpoints, fetch once and compare exact `main` and release-line snapshots read-only. Discovery only proposes reviewed fixes. Backport a selected trunk fix or forward-port a release-first fix through its own isolated work branch, renewed evidence, divergence receipt, and protected CAS integration. Keep `main` as development trunk: never reset/repoint it to, track, or replace it with `release/X.Y`.

Create an immutable candidate before builds. Build once, admit exact digests, then promote without rebuilding through one signed annotated exact tag. Ask before external push/publication.

Never author in the main worktree, directly update protected refs, automatically select fixes, make broad tag pushes, delete/move/reuse published tags, or accept fallback artifacts. Rollback redeploys an earlier admitted release; corrections use a new beta/RC/patch identity.

Validation commands: `simple release version-check`, `beta-prepare`, `backport-check`, `candidate-check`, `promote-check`, and `withdraw-check`.

Live rulesets, signing, protected pushes, and publication require explicit authority. A local plan PASS is not live release evidence.
