<!-- codex-design -->

# Release Process Hardening Detailed Design

## Module contracts

### Version policy

`parse_release_version(text)` recognizes stable and numbered lowercase prerelease versions. `validate_version_channel(version, channel)` rejects suffix/channel mismatch. `check_version_projection(expected, name, observed)` returns a stable drift reason. Rendering uses `ReleaseVersion.canonical()`.

### Session policy

`ReleaseSession` contains session ID, workspace path, main-worktree path, work branch, target ref, base SHA, expected target SHA, and policy hash. `validate_release_session` rejects empty identities, equal workspace/main paths, non-`work/` authoring refs, direct protected targets, and missing exact hashes.

### Backport admission

`BackportRequest` fields:

```text
source_commit_sha
change_id
work_id
change_kind
review_receipt_sha256
target_line
expected_target_sha
adaptation_reason
evidence_sha256
result_commit_sha
```

`check_backport_admission` accepts only `change_kind=fix`, `target_line=release/X.Y`, exact nonempty commit/digest facts, and evidence bound after application. Empty adaptation reason is normalized to `none`; ambiguous refs and feature changes reject.

### Candidate

`CandidateManifest` includes canonical version, attempt, ref, commit and source/policy/version/toolchain/support digests. `candidate_identity()` creates canonical length-delimited text for hashing by an outer facade. `check_candidate_manifest` validates ref/version/attempt agreement and all required facts. `check_candidate_create_once(existing_identity, proposed_identity)` accepts absence or exact idempotent equality and rejects mutation.

### Promotion

`ReleaseAdmission` binds candidate identity, commit, artifact manifest digest, evidence manifest digest, and admitted flag. `PromotionPlan` includes exact tag, commit, signed/annotated flags, exact-push flag, rebuild flag, fallback flag, and artifact digest. `check_promotion_plan` requires admission and exact equality, `signed && annotated && exact_push`, and `!rebuild && !fallback`.

`withdrawal_plan(version, redeploy_version, delete_tag, move_tag, reuse_version)` rejects destructive identity changes and otherwise returns an auditable non-mutating plan.

## CLI

Extend `simple release` with pure commands first:

```text
version-check --version=... --channel=...
beta-prepare --version=... --target=release/X.Y --target-sha=... --session=...
backport-check --source-sha=... --change-id=... --work-id=... --kind=fix ...
candidate-check --version=... --attempt=N --commit=... <digest flags>
promote-check --tag=v... --commit=... --candidate-commit=... --signed --annotated --exact-push --no-rebuild --no-fallback
withdraw-check --version=... --redeploy=...
```

Human output is concise. `--json` uses stable status/reason keys. Commands check/plan only; they do not invoke Git/GitHub/signing/build.

## Policy schema changes

Upgrade `.spipe/policy/vcs.sdn` to `spipe-vcs/3`: mandatory unique branch/workspace session authoring; rebase matrix; create-once candidate; exact tag push; immutable signed annotated tags; release/backport authorities; drift fingerprint. Add `release/policy.sdn`, `release/support.sdn`, and `release/legacy-tags.sdn` only when their parsers/checkers are implemented; do not add declarative files that no shipped command reads.

## Spipe plugin

The plugin manifest and JSON/package/protocol identities move together to `0.2.0`. Capabilities and schema declarations are mirrored. Add canonical general software-release guidance and project it into all model surfaces. Extend `scripts/build.shs` with bounded checks for version parity and forbidden unsafe phrases/commands. Initial CLI/MCP release operations expose policy/status/plan documents; mutation waits for a capability-bound provider.

## System scenarios

The executable scenario uses the frozen manual steps:

1. `Load the canonical release policy`
2. `Prepare an isolated beta release`
3. `Admit reviewed bug-fix backports`
4. `Freeze and qualify the release candidate`
5. `Promote exact admitted artifacts`
6. `Withdraw without rewriting release identity`

Each primary step has success and adjacent rejection assertions. Advanced projection/plugin parity detail is folded. The manual shows commands, expected typed reasons, and recovery behavior without raw test code dominating.

## Migration

1. Land pure types/checkers and focused specs.
2. Route CLI plan/check commands to them.
3. Remove unsafe tag/direct-main text from legacy `prepare.spl` and skills.
4. Update plugin version/capabilities/projections/parity gate.
5. Convert external CI/provider mutation in a separately authorized lane; until then, current tag-triggered publication is documented as not admitted by the new release process.

## Runtime boundary decision

`runtime_need: none` for this implementation slice. `facade_checked`: existing release GitHub/process owners were inspected. `chosen_path: reuse-facade` for future execution, while current work remains pure planning. `rejected_shortcuts`: direct `rt_*`, raw Git subprocesses, main-worktree mutations, fixture-only success branches, and provider field pokes.
