# RC phase3 release-route contract is inconsistent

- Canonical bug tag: `BUG-RELEASE-PHASE3-ROUTE-CONTRACT-20261011`
- GitHub: https://github.com/ormastes/simple/issues/3129
- Severity: P1
- Status: OPEN; candidate HOLD; authorized branch/ancestry policy unresolved.

Reviewed candidate tree `ab54d5b695b6275ad1199de174229a936a262cb8` combines local `26b790634335575981af5ccc8999082516e0c966` with remote `13ca99671234295dae05e919de105b341870c8ae`. The candidate delta SHA-256 is `f9e6b8aaeb1ccd7245bab5eb7329eccfda896a067bc99f7980c0d9d529a52e80`. This metadata repair is based on local 26b7; it does not integrate or accept that candidate.

Two conditions share one inconsistent route contract:

1. `release/version.sdn:4` is `1.0.0-rc.1`. The candidate workflow at lines 317–319 selects `release_phase3`; the convergence manifest at line 3 names `release/1.0`. Admission lines 345–354 require exact release_ref equality. The phase3 dispatch therefore rejects this exact manifest. Dispatching the other branch would describe a different integration target.
2. Candidate workflow lines 317–335 permit main absorption on the designated phase3 line. Admission lines 109–116 and convergence-checkpoint.shs lines 64–67 reject main being an ancestor of release. For a phase3 history that absorbs main and then gains release-only commits the candidate rule permits the history but its mandatory receipt cannot be produced. This source counterexample does not assert current hosted ancestry: the review store lacked the manifest main SHA.

The checked-in release-lines ruleset patterns select `release/*` and `release/**/*`, not `release_phase3`. The review broker still requires actual live ruleset association and fails closed. Live protection was not queried or changed; alias recognition is not proof of coverage.

The authorized RC integration branch and allowed ancestry must be explicitly settled before candidate selection, admission, checkpoint, manifest provenance and protection can be aligned. Do not weaken gates, waive receipts/provider checks, relabel historical classifications, or use a manifest for another branch to force integration. No promotion policy is selected or authorized by this report.

The independent source review covered 14 workflow/sanity/bootstrap/document paths. Four Rust/library paths were separately assigned; no full-candidate acceptance is claimed. Manifest owner-attestations and historical/native PASS statements do not qualify this exact candidate. Workflows, tests, compiler/native jobs and publication remain UNRUN. Closure requires reviewed source alignment and normal exact-ref/head/provider evidence and protected admission/qualification.

Evidence: `reviews/remote-13ca-after-26b7/workflow-release-independent-review.md` and `independent-18-path-review.md` in the retained phase3-whole-20261011-c06 evidence root. Existing issue search found #1603 about whole-trunk gate ranges and hook skew; that is distinct from this alias/ancestry contract. No main source/index/ref or allocated probe was changed.
