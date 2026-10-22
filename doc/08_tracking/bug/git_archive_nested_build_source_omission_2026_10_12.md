# Git archive drops tracked nested build sources

Status: source fix applied locally; archive acceptance passed. Native worker qualification remains pending. Bug DB reconciliation pending: no qualified DB writer was available. Canonical ID: `git_archive_nested_build_source_omission`.

The root `.gitattributes` rule `build export-ignore` matches directories named `build` anywhere in the tree. A committed source capsule exported from revision `40ec45ca95e5b899983ece4d4ad8b17dfa35958d` therefore omitted 24 tracked files under nested build directories. Its manifest accurately described the incomplete archive, but did not compare archive membership against the committed requested roots.

The Phase1 native-worker build reached 522 newly compiled modules and 534 cache hits, then failed three modules. One failure was `app.io._CliCompile.compile_targets` importing `app.build.targets.action_identity`: the valid committed source was absent from the capsule. The resolver's final relative-path diagnostic was a consequence, not evidence that the absolute import syntax was wrong. The other two source failures have separate owners. This report does not mark the worker build or any native test product passing.

## Repair

Anchor the five repository-root cache exclusions: `/build`, `/tmp`, `/artifacts`, `/node-compile-cache`, and `/system`. Preserve the existing path-qualified vendor/generated exclusions. Only `build` caused omissions in the audited requested roots; the other four unanchored rules have the same structural hazard.

Upstream commit `53539789cba` already anchors `/build` and `/system` on `origin/release_phase3` (observed tip `75480f80e648e02b6df800f610283b2e07dad854`). The current private acceptance baseline predates that repair. Any new upstream change must contain only the three remaining root-cache anchors plus owned regression/report material; do not duplicate the two existing fixes. The old source2 capsule still requires provenance-safe replacement.

Source snapshot preparation must compare the explicit committed requested-root inventory against the exported inventory. Any intentional exclusion needs an explicit policy reason. Pin each resulting blob and record generated composition sources separately. An archive command returning zero and a hash manifest of its output do not establish completeness.

## Acceptance and evidence

Packet: `build/native_probe/archive-export-scope-20261012-sol/`.

- `OMISSION_AUDIT.json`: 16,992 committed files across the seven requested source roots, 24 missing from the original archives; each missing path has its original Git blob ID and SHA-256.
- `verify_archive.py`: actual isolated Git-tree/archive regression, using the original committed `.gitattributes`, the real committed `action_identity.spl`, root exclusion fixtures and nested source fixtures for all five names. The shared index and old capsules are untouched.
- `RESULT.json`: baseline/candidate results plus complete candidate requested-root membership. `CANDIDATE_SOURCE_MANIFEST.json` pins the repaired inventory. Candidate archive is diagnostic source evidence, not a promoted compiler source capsule.
- Actual result: baseline 5 passed / 6 failed; candidate 11 passed / 0 failed. The complete requested-root export contains all 16,992 committed files, with zero omissions and all 24 recovered blob bytes matching their original committed identities.
- The first harness setup failed before archive execution because Git on Windows read a CRLF alternates line as part of the object path. A second overbroad archive was explicitly stopped before an acceptance result; the final bounded selectors completed the one baseline/candidate acceptance comparison. No compiler invocation occurred in this regression.

Preserve the old immutable source2 capsule, failed receipts and compatible compiled objects. A future successor capsule must name the repaired snapshot policy and new source identities; never rewrite the old cache authority to pretend the omitted sources were previously present.

Expanded upstream regression: actual Git archives retain the 26 existing tracked regression inputs and synthetic nested source bytes under all five cache names; all five root cache fixtures remain excluded. The baseline reproduces the nested omissions. This does not qualify any compiler or test executable.
