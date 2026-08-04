# Feature: Robust Lifecycle Persistence Convention Cleanup

## Raw Request
`$sp_dev impl and update what is not matched simple convention and unneeded grammar addition. sync gh and check robust_lifecycle_persistence_desing...md. check and update to consistent current simple grammar and convention.`

## Task Type
code-quality

## Refined Goal
Bring the robust lifecycle persistence design lane and its implementation into conformance with the current Simple language conventions by removing any unnecessary proposed grammar and synchronizing the verified change with GitHub.

## Acceptance Criteria
- AC-1: The referenced robust lifecycle persistence design artifact is identified and reviewed against the current syntax quick reference and `$coding` rules.
- AC-2: Every syntax example and implementation file owned by the lane uses current Simple conventions, including `val`, `<>` generics, `if val` pattern binding, constructor calls, standard imports, and supported compact grammar.
- AC-3: Any grammar addition proposed solely for this feature is removed from design, requirements, implementation, parser/compiler code, and tests unless existing language behavior demonstrably cannot express the requirement.
- AC-4: Lifecycle persistence behavior remains covered by focused executable evidence; changed SSpec sources have current mirrored Markdown manuals and no executable specs exist under `doc/06_spec`.
- AC-5: Focused checks, changed-file lint, duplication/stub guards, direct env/runtime guards, and applicable compiler/core checks pass once without placeholder assertions or silent no-op helpers.
- AC-6: Documentation and process references affected by the cleanup are consistent, with unrelated dirty work preserved and excluded from the lane.
- AC-7: The verified lane is committed, rebased linearly on `main@origin` with the file-count guard, and pushed to GitHub main.

## Scope Exclusions
Unrelated dirty files and active workspaces are outside this lane. New language grammar is outside scope unless the existing language cannot represent an accepted lifecycle-persistence requirement and the user explicitly selects such an expansion.

## Cooperative Review
N/A: this is a narrowly scoped convention and grammar-removal audit; one merge owner can review the complete diff and focused evidence without splitting interfaces or manual flow helpers.

## Phase
verify-warn; sync-ready

## Log
- dev: Created state file with 7 acceptance criteria (type: code-quality).
- implementation: Preserved the original synthesis under `doc/01_research/domain/language/lifecycle/`, replaced the design with an existing-Simple library model, and added requirements, architecture, guide, implementation, SPipe scenarios, and a generated manual.
- runtime decision: `runtime_need=none`; `facade_checked=std.common` and the default `std.lifecycle_persistence` family surface; `chosen_path=reuse-facade`; `rejected_shortcuts=new grammar, raw rt_* access, duplicate EntityRef, parser-only evidence`.
- diagnostic evidence: the focused scenario passed 4/4 and docgen produced 108 documentation lines with 0 stubs using the Rust seed only because the deployed `bin/simple` currently identifies as a bootstrap seed. This is not final verification evidence.
- blocker: the available self-hosted `simple-bootstrap 1.0.0-beta` artifact lacks the `check` and `sspec-maintain` commands; final pure-Simple verification remains pending.
- refactor: Added the library guide/TLDR, architecture/research TLDRs, and corrected `.claude/skills/spipe.md` from deprecated `lib`/`reliable` tier names to current `strict`/`robust`/`critical` terminology.
- sync: Rebasing the isolated lane from `6b7f` onto current `main@origin` `c76` completed without conflicts; the jj file count increased safely from 110162 to 110164.
- verifier build: Current-main no-stub full-CLI build failed fast with `MirToLlvm` missing `MirTextCodegen.translate_block`. The same owner family is already tracked by `doc/08_tracking/bug/mir_to_llvm_translate_call_trait_break_2026-08-04.md`; no compatibility shim was added because it would undo the index-preserving backend change.
- last-good build: An isolated build from documented last-good `5687d7fc9558` remained pre-object at ~99% CPU and ~2.4 GiB RSS for 15 minutes with no progress receipt. It was terminated at the bounded checkpoint; log retained at `/home/ormastes/dev/pub/simple-verifier-last-good/build/native_probe/simple_verifier_last_good_build.log` and no cache objects were discarded.
- verify blocker: Current `main` cannot build the required pure-Simple verifier until the in-flight `MirTextCodegen`/`MirToLlvm` contract is reconciled. Seed-only diagnostic PASS remains non-promoting and GitHub push remains intentionally pending.
- blocked audit 3: Fetched and rebased cleanly onto `main@origin` `dd1d`; file count increased safely from 110164 to 110166. `MirTextCodegen` still requires `translate_block` and `translate_call`, `MirToLlvm` still provides neither compatible method, the tracked bug remains OPEN, and deployed `bin/simple` remains the Rust seed. This is the third consecutive goal turn with the same final-verification blocker.
- resumed fix: An owner-level inherent-implementation repair passed the focused 19/19 regression and moved the no-stub build beyond the former semantic abort. During the final rebase, `main@origin` supplied a concurrent, better contract-compatible fix with pristine-worktree evidence; this lane dropped its alternate compiler edits and preserved the upstream resolution.
- resumed verifier build: The no-stub full-CLI build passed the former semantic abort and remained CPU-active in native compilation, but produced no cache objects or progress receipt by the bounded 15-minute checkpoint. It was terminated once; the cache and `build/native_probe/robust_lifecycle_cli_build.log` were preserved and the command will not be repeated this session.
- compiler-wide check: The canonical `check src/compiler` path reproduced the already tracked per-file diagnostic startup blocker. Its default worker hit the 60-second CPU guard; the supported 300-second override still spent more than two minutes on the first delegated file. The bounded run was stopped and evidence appended to `bootstrap_diagnostic_multifile_check_startup_blocker_2026-08-02.md` instead of allowing an hours-long sweep.
- final rebase: Rebasing onto `main@origin` `14b0b` increased the tracked file count safely from 110166 to 110264. A single documentation conflict revealed that upstream had already merged a stronger trait-compatible compiler fix; the alternate local compiler change and regression were dropped, leaving no compiler source delta in this lane.
- final audit: Focused lifecycle behavior remains 4/4 PASS, generated manual remains 108 lines with 0 stubs, owner-regression evidence was 19/19 during blocker diagnosis, direct-runtime guards and changed-file diagnostics passed, and the targeted placeholder/unwanted-grammar scan found only prose explicitly documenting rejected syntax. Final status is WARN rather than PASS because the deployed binary identifies as the Rust seed and the pure-Simple full CLI build hit the bounded opaque pre-object checkpoint.
