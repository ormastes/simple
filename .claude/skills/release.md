# Release Skill

Perform a version bump and release of the Simple Language compiler.

Require verified SPipe/manual evidence and one release-bound `bin/simple test test --whole --mode=interpreter` PASS. Work only in one isolated release session with a unique branch and worktree. Beta work targets `release/X.Y` and admits only explicit reviewed bug-fix backports with exact stable patch-ID equivalence, provider-bound review/check receipts, and renewed result-revision evidence. Adapted patches fail closed until a separately reviewed equivalence protocol exists.

```
/release              # patch bump (default): 0.9.2 → 0.9.3
/release patch        # same as above
/release third        # same as above
/release minor        # minor bump: 0.9.2 → 0.10.0
/release second       # same as above
/release major        # major bump: 0.9.2 → 1.0.0
/release first        # same as above
/release 1.0.0        # set exact version
```

## Procedure

Given argument: `$ARGUMENTS`

Validation commands: `simple release version-check`, `beta-prepare`, `backport-check`, `candidate-check`, `promote-check`, and `withdraw-check`.

### Step 1 — Determine new version

Live rulesets, signing, protected pushes, and publication require explicit authority. A local plan PASS is not live release evidence.
