# ft29-6: spipe home routes (Git Bash symlink copy) and semantic link lint remote URI form

Status: verification-pending (fix landed; not yet verified on the pure-Simple native runner)
Date: 2026-11-28

## 1. spipe_home_routes_spec "connects core and private homes..." (expected 3 to equal 0)

Root cause: `scripts/setup-spipe-local.shs` creates the core routes with `ln -s`.
Under Git Bash/MSYS the default (`MSYS` without `winsymlinks:nativestrict`) makes
`ln -s` COPY the directory, so the route never resolves to the core and setup
exits 3 ("does not resolve to ..."). Real product bug on Windows hosts, not a
spec premise problem.

Fix: the script exports `MSYS=winsymlinks:nativestrict` on MINGW/MSYS/CYGWIN so
`ln -s` makes a real link or fails loudly. No-op elsewhere.

Repro/prevention: new `--symlink-only` scenario in
`spipe_home_routes_contract_test.shs` (asserts `test -L` on both routes) and a
new spec example "links core routes with real symlinks rather than copies".
Repro failed before the fix, passes after.

## 2. semantic_link_lint_spec "should diagnose and fix local fragment colon and GitHub range destinations"

Root cause: outdated spec premise (spec header: "authored before implementation. UNRUN").
`plan_semantic_markdown_links_v1` passes `remote` as `package_qualified` to
`semantic_links_from_lines_v1`, so GitHub destinations deliberately become
`spl://<pkg>/<module>#fn:<name>~<fp>` (resolvable outside the repository), while
repository-local links stay `spl:fn@sample.value~<fp>`.

Fix: spec updated to the current design; asserts both exact forms and that the
reference definition is NOT the short form (prevention). No product change.

## Notes
Other examples in the same spec failed only in the dirty shared checkout
(private-fn visibility, 49:83 vs 50:84 offsets) and are outside this lane.
