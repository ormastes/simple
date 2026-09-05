<!-- codex-research -->
# Domain Research: Mandatory-Check Tiering

## Findings

Git defines `pre-push` as a local veto over exact ref updates supplied on
stdin; a nonzero status aborts the push, while `--no-verify` bypasses the hook
entirely. It is therefore suitable for bounded feedback but not a substitute
for an independently enforced remote release gate. Git changes to the active
non-bare worktree before running client hooks. Linked worktrees have private
Git directories but share common repository state, including the default hooks
directory, so a common hook must resolve the active worktree at invocation
rather than embed the installer checkout. Git provides `--show-toplevel`,
`--git-common-dir`, and `--git-path` for those distinctions.

Sources: [Git hooks](https://git-scm.com/docs/githooks),
[Git worktree](https://git-scm.com/docs/git-worktree),
[repository layout](https://git-scm.com/docs/gitrepository-layout), and
[rev-parse](https://git-scm.com/docs/git-rev-parse).

Stage-specific hook systems support the same separation explicitly. The
pre-commit framework distinguishes automatic stages from a `manual` stage and
supports selective hook IDs. This favors named push and bootstrap tiers with
visible per-gate status instead of one opaque all-or-nothing local command.
No primary source prescribes a universal ten-second hook limit; ten seconds is
therefore a project NFR that must be measured directly.

Source: [pre-commit hook stages and skipping](https://pre-commit.com/#confining-hooks-to-run-at-certain-stages).

Content-addressed systems treat cached results as reusable only when all
declared semantic inputs match. Bazel hashes action inputs and outputs and
checks immutable cache entries before executing a miss. GitHub and GitLab cache
keys likewise use content-derived keys, but both document caches as optional
optimizations rather than proof that verification ran. A missing or stale
cache must execute or remain unfinished; it cannot become PASS.

Sources: [Bazel remote caching](https://bazel.build/versions/8.3.0/remote/caching),
[Bazel best practices](https://bazel.build/docs/best-practices),
[GitHub dependency caching](https://docs.github.com/en/actions/reference/workflows-and-actions/dependency-caching), and
[GitLab caching](https://docs.gitlab.com/ci/caching/).

in-toto and SLSA provide stronger receipt semantics. An attestation binds an
immutable subject digest to a typed claim; validation checks statement type,
subject, signer/trust policy, and digest. SLSA provenance records parameters,
resolved dependencies, producer identity, and output digests, and distinguishes
completeness, authenticity, and accuracy. For this repository, each ledger row
therefore needs a stable gate identity, exact input/source and policy identity,
command/tool identity, verdict, time, and content-addressed evidence. Receipt
existence alone is insufficient.

Sources: [in-toto Statement v1](https://github.com/in-toto/attestation/blob/main/spec/v1/statement.md),
[in-toto validation](https://github.com/in-toto/attestation/blob/main/docs/validation.md), and
[SLSA requirements](https://slsa.dev/spec/v1.1/requirements).

Freshness must fail closed. TUF rejects expired or older metadata and
hash/version mismatches rather than guessing. GitHub required checks similarly
bind acceptance to the latest commit SHA. A must-check ledger should invalidate
on source, command, policy, schema, toolchain, or relevant configuration
changes; `absent`, `running`, `failed`, `stale`, and `invalid` are distinct from
`pass`.

Sources: [TUF specification](https://theupdateframework.github.io/specification/v1.0.26/)
and [GitHub required-check troubleshooting](https://docs.github.com/en/pull-requests/how-tos/merge-and-close-pull-requests/troubleshooting-required-status-checks).

Remote orchestration should keep its required umbrella workflow present while
conditionally selecting expensive jobs inside it: GitHub warns that a required
workflow skipped by path filtering can remain Pending. Concurrency groups can
cancel superseded same-ref bootstrap work. These mechanisms reduce duplicate
cost without relabeling skipped work as evidence.

Sources: [GitHub workflow path filters](https://docs.github.com/en/actions/reference/workflows-and-actions/workflow-syntax#onpushpull_requestpull_request_targetpathspaths-ignore)
and [workflow concurrency](https://docs.github.com/en/actions/how-tos/write-workflows/choose-when-workflows-run/control-workflow-concurrency).

NIST recommends complementary automated techniques rather than one broad
success label, and its SSDF calls for collecting and securely retaining
provenance and integrity information for release components. This supports a
registry with explicit gate IDs and retained evidence, where missing mandatory
members prevent aggregate completion.

Sources: [NIST IR 8397](https://csrc.nist.gov/pubs/ir/8397/final) and
[NIST SSDF SP 800-218](https://csrc.nist.gov/pubs/sp/800/218/final).

## Implications for the selected requirements

- Keep the push tier bounded and measured locally; retain bootstrap and release
  authority outside the bypassable hook.
- Install a shared worktree-resolving launcher, never an absolute dispatcher
  path from one checkout.
- Fingerprint all semantic inputs and rehash retained evidence; a cache hit or
  existing path is not PASS by itself.
- Preserve explicit unfinished states with owners and unblock conditions.
- Bind remote acceptance to the latest commit and cancel superseded expensive
  runs rather than weakening their verdict.
