# Private-import baseline: sparse source and CI base failures

Status: scoped gate repair verified locally; hosted CI and reviewed landing follow in the PR. No private-import baseline entries or language rules are waived.

The required-gate checkout omits source directories. The old checker read only working-tree files, incorrectly marking their private declarations stale (20,194/20,194 entries in the isolated reproduction; historical CI cones differed). After that defect was addressed, CI still lacked `origin/release/1.0.0`, so implicit merge-base lookup failed.

## Repair

Read present sources from the working tree. For physically absent skip-worktree paths only, use one batch `git checkout-index` into a private temporary directory and scan those indexed declarations. The checkout and index remain unchanged. Do not skip baseline rows: an indexed promotion/export/removal must still fail. Do not fall back for a present directory, unreadable file or dangling symlink. Index/checkout failures propagate as errors.

Use the trusted PR event base through `PRIVATE_IMPORT_BASE` in the required-gate workflow; an explicit `--base` overrides it. The pre-push dispatcher supplies its already computed outgoing-range base directly. Keep the base-pinned manifest selection unchanged. Reject an unreadable base commit rather than treating it as an introducing change.

## Reproduction and adjacent prevention

The original checker returned exit1 with all20,194 entries falsely stale in the isolated sparse worktree. The candidate checked all20,194 with zero stale/added entries, both via explicit `--base` and the CI environment path. Selftests execute real temporary Git repositories: private declaration and baseline shrink positives; public/exported/deleted/added entry negatives; empty baseline; invalid base; actual tracked deletion without any sparse entries; omitted indexed private declaration; indexed public promotion and empty source; present sparse directory and dangling symlink; corrupt index and unavailable indexed blob. They also assert that scanning does not rematerialize the checkout.

Astra reproduced two fail-open alternatives in #7514: an empty sparse-list file combined with `NR==FNR` swallowed real deletions, and skipping sparse entries hid indexed promotions. The replacement uses explicit `FILENAME == ARGV[1]` and actually reads indexed sources. Astra then caught a directory/read-error fallback in the first replacement; the physically-missing filter and real regression controls address it. The implementation remains shell/awk/Git, with no Python runtime dependency or executable-mode change.

This supersedes the attempted gate repairs #7508/#7514 after merge. It does not claim unrelated compiler/runtime verification. Canonical selftests run before each gate invocation; full current-baseline scans are not repeatedly rerun outside changed-source validation and normal hooks/CI.

## Baseline object-read hardening

The advanced #7508 head05ba341a74e03d0decaa77bdb546aa2af1c273d4 supplied another valid counterexample after #7523 landed: a readable base commit whose tree still names an unavailable baseline blob was mistaken for an introducing change, allowing newly added rows. Astra reproduced the false PASS and the alternative's correct ERROR. Port the needed logic in shell/Git: inspect the base tree, permit the introducing skip only for an absent path, require a blob, and propagate object-read/sort/comparison errors. A real temporary-repository regression removes the base blob while adding a valid row and requires ERROR2; a separate empty-tree commit verifies genuine introduction still passes. This credits the useful #7508 hardening without replacing the landed shell scanner with a Python dependency.
