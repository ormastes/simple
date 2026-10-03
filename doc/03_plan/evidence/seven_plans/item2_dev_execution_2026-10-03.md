# Item 2 development execution and remaining gates

Date: 2026-10-03. Scope: Simple distributed textual databases (SCV + jj + GitHub),
seven-item plan item 2. Selected scope remains Authority A / Adapters A /
Operating B / Retention A, all REQ-001–036 and NFR-001–015.

**STATUS: INCOMPLETE. No production verification PASS or executed TDD RED/GREEN.**

## Isolation and inputs

Owner: Codex root; session `item2-tdd-20261003`; integration worktree
`C:/dev/simple-item2-tdd-20261003`; branch `work/item2-tdd-20261003`;
target `release/1.0`. The initial inspected release commit was
`e9cd3153c881c55f59eaaa2573b4b8a5e803023a`. The private integration branch was
rebased onto fetched target `cb2f783acf0ea22e8da54ff0d8d18b4fb14c816c` before
integrating lane commits. The private Git worktree directory contains the
session owner/base/expected-target record.

Parallel lanes used separate linked worktrees and `work/item2-*` branches:

| Lane | Inputs delivered for integration | Responsibility |
|---|---|---|
| Research | `e1d0c507239` | Append-only local/domain research, architecture and design |
| Specs | `4f78befb590` | Concrete acceptance matrix, test/task plans, pure prerequisite scenarios and manual status |
| Implementation | `fa4362757ea`, `9e961bb70a9`, `4bfd90bcda9` | Additive Git history read-back, integration scenarios, root-scratch correction |
| Independent review | Separate `simple-item2-review-20261003` worktree | Reviewed source and evidence boundaries; root integrates corrections |

The existing dirty command files in `C:/dev/simple` and other sessions' item 1,
item 5 and bootstrap worktrees were not included or modified.

## What changed

The [acceptance matrix](item2_acceptance_matrix_2026-10-03.md) specifies concrete
fixtures, actions, independent oracles, production owners and evidence classes
for all 51 selected requirements/NFRs. Five compound campaigns cover two-clone
offline edits/conflicts, interruption/retry, resnapshot recovery, SJ lease
ownership and host parity. Existing broad acceptance cases remain fail-fast;
three added pure identity-map scenarios do not prove durable acceptance.

The additive `db_git_settlement_reconcile_history` uses a secure external bare
scratch repository, exact advertised-OID fetch, at most 32 cursor inspections,
raw single-parent history and final authority read-back. The old conservative
API is unchanged. `published` means transport ancestry inclusion only, not
signed receipt/accepted-batch admission. Scratch root `/`, checkout/common-dir
overlap, redirected Git environments and unproved Windows canonical paths are
rejected before scratch creation. Only a successfully created, identity-checked
scratch child may be removed.

Positive history assertions require their specified result on every supported
host. The integrated tests do not accept `SCVDB_SCRATCH_SCOPE` as an alternative
passing outcome on Windows; that current capability gap must make those cases
fail when executed. Invalid-scratch rejection tests remain separate negative
oracles. This keeps the desired final behavior intact instead of qualifying
an unsupported host through an easier assertion.

## Evidence and limitations

| Check | Observed result | What it proves |
|---|---|---|
| Lane diff checks | Passed for delivered changes | Whitespace only |
| Integrated env/process guards | `--working` and `--staged` both PASS using a private comparison index at the fetched release base | Changed app leaf uses facade boundaries; not runtime behavior |
| Git-only protocol experiment | Exact advertised-OID fetch at depth 33, raw parent inspection, no FETCH_HEAD | Git protocol feasibility, not Simple execution |
| Independent source review | No confirmed P0/P1 at `fa4362757ea`; root-scratch P2 identified and corrected in follow-ups | Source review only; no merge admission |
| System spec inventory | 156 scenarios, including 153 retained fail-fast broad cases | Scope remains visible; not runtime coverage |
| Simple compile/type/test | BLOCKED_RUNTIME | No RED/GREEN result or runtime correctness claim |
| Manual | Explicit unexecuted addendum | Admitted docgen and generated-manual verification remain pending |

The limited independent follow-up confirmed that `4bfd90bcda9` rejects canonical
root before allocation and resolves the P2 at source level; the intermediate
prefix-only fix was insufficient. The added assertion is still unexecuted.
Integrated source inspection counted 51 matrix rows, 156 system scenarios and
153 broad fail-fast calls. The tracked `doc/06_spec/*_spec.spl` count was zero.

The Git experiment used the isolated local fixture
`C:/Users/user/AppData/Local/Temp/item2-protocol-cccb39f4fb0447948304517961ca1b5a`.
Its result must not be reused as evidence that the Simple adapter compiles or
executes. The source-preservation test currently samples HEAD/refs/status,
index hash, fixture content, object counts and a FETCH_HEAD sentinel; it does
not yet prove complete source/common-directory manifest equality.

## Runtime blocker, observed in this session

No deployed `bin/release/**/simple.exe` was present in the main checkout or
inspected Windows bootstrap worktree. The historical Windows and WSL runner
paths recorded by the September 29 item 2 evidence did not exist. WSL Ubuntu's
`/root/simple-build` exposed phase-1 snapshots and a Rust bootstrap generation,
not an admitted full self-hosted test runner in the inspected locations.

A live bootstrap process used
`C:/Users/user/.simple/worktrees/simple-windows-phase2/build/bootstrap-llvm80/stage3/x86_64-pc-windows-msvc/stage2-runtime-authority/simple.exe`.
A separate `--version` probe produced no output for over 60 seconds and was
stopped by its exact PID 29880. That observation does not establish a compiler
defect or prove the binary's pedigree. No acceptance tests were run with it;
the other session's bootstrap process was left untouched. Its adjacent hosted
runtime and Cargo fingerprint receipts do not establish pure-Simple admission.

At 08:29:56 KST the external bootstrap wrote `native-command-result.env` under
`build/native_probe/llvm-integrated-native-78d5-attempt1`: `raw_status=0`, source
`78d5a1cd7768f70cc42a56888ef3a799823bd738`, and explicitly
`admission=UNADMITTED`. Its log reports a linked 19,513 KiB stage-2 binary at
`stage2-resume.f7iZK3/stage2/x86_64-pc-windows-msvc/simple.exe`. The producer PID
28048 had exited; collector PID 26892 and shell children remained live when
inspected. A successful link is not a full CLI/test-runner admission. This newer
evidence supersedes any assumption that the build is still compiling; it does
not supply the missing Simple test receipts.

A separate bounded probe of that **new** binary exited 0 and printed
`simple-bootstrap 1.0.0-rc.1`. Its SHA-256 was
`aaf13da5942425e19b1aba2ed4b6d272687de1d4710ad7200ed0621d96990879`.
The `bootstrap_main.spl` dispatcher advertises `compile` and `native-build`,
not the full `test`/`check` CLI. This is useful bootstrap progress and does not
admit a full SSpec runner or replace the remaining acceptance checks.

Before resuming execution, locate a completed, provenance-verified self-hosted
runner and its admission receipts. Do not substitute a Rust seed or translate
the tests into another implementation and call that TDD evidence. Related
historical bootstrap debt is tracked in
[Windows full CLI unresolved symbols](../../../08_tracking/bug/windows_stage2_cli_stubbed_symbols_2026-09-25.md);
that older report alone does not diagnose the current probe.

## Remaining work, in dependency order

1. Execute new integration assertions against the recorded pre-implementation
   version, preserving an actual failing result; execute the same assertions
   against the candidate after the production change. Since source was drafted
   while execution was blocked, describe this as retrospective regression
   evidence, not a completed test-first RED/GREEN loop.
2. Add deterministic moving-authority and failed-fetch injection; prove complete
   source/common-directory preservation and cleanup/error paths. Measure total
   operation time and transfer/storage bounds; a cursor count is not an RSS or
   byte quota.
3. Implement alias-safe final-path resolution in the existing host path owner,
   then run the same successful history cases on Windows. Safe rejection is an
   interim limitation, not fulfillment of REQ-036. Qualify other supported hosts.
4. Implement the remaining selected pure core, durable transaction, protected
   publication/receipt, CI/bridge, retention and resnapshot owners in the updated
   design's order. Replace each broad fail-fast case only with its full oracle.
5. Run required env guards, runtime/core/MCP smoke checks where applicable,
   admitted docgen, full acceptance and Operating-B measurements. Observe the
   three-cycle cap; do not rerun unchanged green checks.
6. Review the integrated exact head, inspect PR comments/checks, land through a
   PR to the requested release line only after its gates are met, and arrange
   the required main forward-port. No protected ref or release tag is directly
   updated; no publication has occurred.

The objective remains active. Documentation and a source candidate are useful
progress but do not satisfy the requested fully implemented, tested result.
