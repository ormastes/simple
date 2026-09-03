# macOS M4 Workflow Readiness Audit — 2026-09-02

## Verdict

**Local workflow/schema readiness: PASS. Hosted native execution readiness: BLOCKED.**

The M4 and M5 workflows are absent from the GitHub default branch (`main`), so
GitHub cannot dispatch either workflow. No workflow was pushed and no hosted-run
or native arm64/x86_64 evidence is claimed.

## Hardened Contract

- M4 artifact names bind architecture, workflow run ID, and run attempt.
- M4 and M5 uploads fail on missing files and retain artifacts for 30 days.
- M5 requires distinct arm64/x86_64 workflow runs and exact run attempts.
- M5 checks out the exact source revision admitted by both M4 receipts.
- M5 binds supplied artifact names to immutable M4 receipt fields.
- M5 compares the thin-bundle evidence manifest with the separately downloaded
  retained evidence manifest before composition.
- M4 receipt admission covers target identity, SDK, deployment target,
  Xcode/clang evidence, provider archive/member/payload digests, and all workflow
  provenance fields consumed by M5.
- A local readiness checker includes mutation-red cases for run-attempt naming,
  runner separation, source pinning, retention, and receipt-schema drift.

## Evidence

- `sh scripts/check/check-macos-m4-workflow-readiness.shs --self-test`: PASS.
- `sh scripts/check/check-macos-universal-m5.shs`: PASS as portable structural
  evidence; explicitly not native release authority.
- Shell syntax, YAML parsing, and focused `git diff --check`: PASS.
- Default-branch local check: exit 3; both workflow files absent from
  `origin/main`.
- `gh workflow view ... --ref main --yaml`: HTTP 404 for both M4 and M5.

## Remaining Hosted Gate

After reviewed changes reach `main`, dispatch two separate M4 runs on native
arm64 and x86_64 runners, retain their exact run-attempt-qualified artifact
names, then supply those names, run IDs, attempts, and shared source revision to
M5. Apple signing/notary evidence remains a separate native service gate.
