# DevHub release/dev repair and actual launch

Status: active; 2026-10-30. Owner /root; fix reviewer Astra; build executor Luna.

## Goal
Repair DevHub and necessary Simple/library defects, build and test the real product, launch it, and land the reviewed fixes on the user-selected release development base.

## Acceptance criteria
- AC-1: Confirm target base. Exact remote release/dev is absent; release/1.0.0 exists. User branch choice pending; diagnosis proceeds independently.
- AC-2: Claim and reproduce the outstanding secured database key-session failure before source edits; fix the proven pure-Simple owner and cover an adjacent failure.
- AC-3: Use an existing provenance-admitted compiler, isolated outputs and strict guards for real native construction. Record source, compiler and output identities.
- AC-4: Execute the production Messenger read path against an independent encrypted fixture, including negative controls and unchanged source evidence. Help output alone is insufficient.
- AC-5: Launch actual DevHub and verify a functional surface; preserve any incomplete database, compiler, library or UI criteria explicitly.
- AC-6: Refresh relevant design/guide, feature/layer wiki, bug/TODO and executable/manual evidence. Workflow docs N/A unless workflow behavior changes.
- AC-7: Complete applicable verification and exact-head Astra review, then merge own PR into confirmed base. No tags/publication requested.

## Current evidence
The clean secured-db worktree starts at 7d0c0219cd2. Its session-close report records a successful native build but failed key-session open before decryption. It is not product PASS. Historical diagnostic iteration counts remain applicable; no unchanged retry is authorized.
GitHub currently reports independent PR 5085 MERGED on 2026-10-28, merge 6011ef9fee09b3ab3fc8d9b069442ed948caaba1 into release/1.0.0. The old admission-rejection handoff is stale.

## Cooperative ownership
Astra owns secured-db diagnosis, claimed bug, pure-Simple repair and regression fixture. Luna owns compiler admission, real build/test/launch evidence; neither may duplicate a passing check. Root owns integration, branch choice and final landing. Existing helper interfaces are retained; new unresolved test oracles must fail closed. Root reviews generated manuals. Main workspace unrelated dirty files are preserved.

## Integration evidence
Current release base fetched as `4efdcb2a7c1d209e77d1d1ea06b095b380c7096e`. Completion head `4beb3d8545a` is its ancestor (git merge-base --is-ancestor exit 0). Secured-db head `7d0c0219cd2` diverges from completion at `842d92702049268524a39e4d11d937e4106da6d4`; replay reviewed DB changes onto current release, preserving upstream changes, before final product construction.

Luna detected and stopped its first product build because the relative-path wrapper compiled from dirty `D:/dev/simple` instead of the isolated worktree. No executable was produced. Retained invalid-evidence log: `D:/dev/simple-devhub-deflate-nlen-20261026/build/devhub-functional-20261030/devhub-build.log`. Next invocation must bind absolute repo, entry, output/cache and producer paths and record source identity before compilation. This failure is not product-build PASS.

Astra diagnostic2 uses retained compiler PID22460 / exec session40183. MIR worker failures alone are nonterminal: historical pinned producer automatically falls back; wait on the same process/session, never restart on that marker alone.

Integration preparation: clean detached current release worktree created at `D:/dev/simple-devhub-integrate-20261030`, base `4efdcb2a7c1d209e77d1d1ea06b095b380c7096e`. Historical callback/cleanup commits `42824ac1ec5` and `0acaabbb4da` applied without conflicts using cherry-pick --no-commit. This is staged, unverified source, not a landed fix. Unreferenced snapshot WIP `da85411fa75` was not imported; its requirements remain open wherever applicable. Await Astra typed diagnostic before freezing final source/build identity.

Diagnostic2 result: native build exit0; fresh production acceptance exit1 with `SQLCIPHER4_MISSING_SECRET` at direct key-session opening before decryption. Fixture main had already required the expected secret environment variable to be nonempty. Independent fixture oracle and encrypted-input/metadata invariants passed; registered storage/Messenger operations remained unreached. This narrows the next distinct diagnostic to SecretRef parsing, environment facade resolution and empty-byte handoff, without logging secret values. No library fix has yet been proven.

## Source review and launch prerequisites
Astra reviewed the staged db_common/codec_registry/sqlcipher4_page/storage_port changes and reported zero new P0/P1 source findings. This is source review only: diagnostic2 failed before the changed callback/cleanup paths executed. Portable overwrite/readback is not a volatile zeroization guarantee; documented residual-copy limitations remain.

Luna found no provenance-bound full DevHub executable in the inspected existing release/completion worktrees. Focused DB fixture executables cannot prove GUI behavior. `build/devhub-release-dev-20261030/BUILD-RECIPE.md` prepares the fresh native build with explicit working directory and paths; it has not run in this integration tree. `doc/08_tracking/bug/windows_devhub_gui_browser_launch_gap_2026_10_30.md` records the source-only browser-opener gap; runtime reproduction remains pending.

Final checks still required: production DB acceptance; actual full DevHub build/launch; applicable runtime/compiler/lib/MCP gates and SSpec/manual verification; exact-head review and merge on confirmed base. No STATUS: PASS or goal completion is claimed.

Diagnostic3 completed build0/run0 for actual SecretRef parse/resolve bytes and adjacent slash/dash/dot forms in a minimal closure. Larger fixture still fails before KDF/page decoding; this does not prove those APIs globally broken or repaired. Three distinct attempts (historical1, full diagnostic2, minimal3) are exhausted. Diagnostic fixture/report/bug evidence copied into integration, retained binaries/logs remain in the original secured-db worktree. No further database diagnostic retry. Independent full DevHub construction/GUI launch proceeds with Luna; all production source stays frozen during that build.

## Blocked handoff

Final changed-source full build failed with one generic-T module; no executable and no actual GUI launch. The async HTTP encoder is repaired and its five native regression checks passed; its prior full-build error disappeared. The database full-context missing-secret failure remains unresolved. Compiler exit0 despite internal failure is separately tracked. No new PR or merge was performed.

The same compiler/database blocking conditions persist across consecutive goal turns. All diagnostic/build processes are terminal. Further permitted progress needs user direction to extend the stopped diagnostic sequence; the async question is pending. The separate branch-base question remains pending because release/dev does not exist. Do not restart unchanged failures, mark this goal complete, or present focused encoder PASS as product readiness.

## User-directed landing

The user explicitly requested "land current impl and done" after reviewing the blocked result. This supersedes continued build/launch work for this session: land the current reviewed implementation and retain open bugs, without claiming product completion or verification PASS. Land through a work branch PR into the existing release/1.0.0 base; release/dev was absent. Do not create a release tag or publish a binary. Preserve remaining compiler, secured-database and Windows launch gaps as follow-up work.
