# Item 4 parallel ownership

## 2026-10-04 SHA dependency continuation

Base: `f5fec9ccf8cb` on release/1.0. Root integrates in isolated
`C:/dev/simple-item4-sha-owner-20261004`, branch `work/item4-sha-owner-20261004`.
Runtime owns core SHA methods and regression intent in its separate sha-core
worktree; acceptance owns independent source/vector review; research owns the
provider-positive design supplement and outer semantic-stream defect report in
its separate provider-docs worktree. Root owns caller migration, documentation,
merge and final status. Lower-model sidecars: N/A.

Shared API agreed before coding: constructor `sha256_stream_v1_new`, mutable
`reset`, `update`, `update_byte`, `finish_hex`, `zeroize`; private mutable
compression and byte-push. Tests use actual owners and fixed digest oracles.
No admitted runtime exists in current evidence. Native tests/docgen/coverage
and full Phase 4 remain UNRUN/FAIL; no passing placeholder replaces them.

Date: 2026-10-03. Initial inspection base and target at allocation:
`e9cd3153c881c55f59eaaa2573b4b8a5e803023a` (`origin/release/1.0`).

Private lanes refreshed to `cb2f783acf0ea22e8da54ff0d8d18b4fb14c816c` before
integration. The intervening change affects the frontend flat-pool codec and
its two tests; inspected linker sources and the research document are unchanged.
Session metadata records this refreshed base/expected target. No runtime PASS
evidence exists to transfer across the rebase.

## Test-first continuation

On the user's `codingtest first` instruction, the same isolated worktrees are
reused with new exclusive ownership: `/root` strengthens the existing image
acceptance spec and updates plan/design; `/root/linker_acceptance` owns the new
`item4_linker_relocation_acceptance_spec.spl`; `/root/linker_research` owns the
new `item4_linker_dynamic_acceptance_spec.spl`; `/root/linker_runtime` reviews
the image assertions read-only. All three specs live under
`test/03_system/app/compiler/feature/`. Helper prefixes are `item4_reloc_` and
`item4_dynamic_` for the new files. Root's image helpers are `item4_read_le`,
`item4_check_elf_load_segments` and `item4_pe_file_offset`.

This ownership amendment applies to this test-first wave; the original lane
table below records the completed research/initial-spec allocation. Runtime
execution and production fixes remain separate pending work.

## Implementation continuation ownership

On `go impl`, `/root` owns ELF parser bounds and its new input-bounds spec;
`/root/linker_research` owns shared-object DT_NULL/string termination and the
dynamic spec; `/root/linker_acceptance` owns the typed native-link result,
wrapper/adapter threading and engine-receipt spec. `/root/linker_runtime` runs
bounded diagnostics in the integration worktree's `build/item4-diagnostic/`
and canonical `build/scv` cache, without editing production files. Root's probe
source is `test/fixtures/linker/diagnostic/item4_linker_probe.spl`.
Research independently reviewed result threading; runtime independently reviewed
the parser bounds. All reviews are source-only unless actual execution receipts
are explicitly attached. The three-attempt diagnostic cap remains in effect.

| Lane / owner | Isolated worktree and work branch | Exclusive edits |
|---|---|---|
| Integration / `/root` | `C:/dev/simple-item4-linker-dev-20261003`; `work/item4-linker-dev-20261003` | Plan/design, acceptance plan, lane ledger, subsequent reviewed production fix |
| Research / `/root/linker_research` | `C:/dev/simple-item4-linker-research-20261003`; `work/item4-linker-research-20261003` | Dated addendum to linker research |
| Acceptance / `/root/linker_acceptance` | `C:/dev/simple-item4-linker-acceptance-20261003`; `work/item4-linker-acceptance-20261003` | New item4 system acceptance spec |
| Runtime reconnaissance / `/root/linker_runtime` | Read-only existing environment; no work branch | No edits or interference with live bootstrap |

All coding agents use the inherited model; no lower-model sidecars are used.
Merge owner: `/root`. Final review owner: `/root` plus an independent same-model
agent after integration; reviewer must inspect the exact final diff and actual
RED/GREEN evidence. No reviewer is assigned to certify unexecuted tests.

Shared requirement IDs are ITEM4-REQ-001 through ITEM4-REQ-010 in
`doc/03_plan/sys_test/item4_linker_acceptance_2026-10-03.md`. Shared helpers are
`item4_load_elf_fixture`, `item4_static_link_error`, and
`item4_archive_with_member_type`; use canonical `std.spec.step`. Missing setup
or unsupported evidence must fail explicitly, never pass a placeholder.

Research commits are integrated before plan reconciliation; acceptance commits
precede production fixes. Each owner reports its exact commit and tests run.
Only owned commits enter the release-targeted integration branch. Existing
main-worktree dirty command files and other item1/item5/bootstrap worktrees
remain outside this change. Refresh the expected target before submission and
renew evidence affected by any rebase. Release refs move only through reviewed
PR integration; this task does not authorize release tags or publication.

## Completion coding wave ownership (2026-10-03)

Root's new branch is `work/item4-linker-completion-20261003` in the existing
integration worktree. Root owns configured request admission, PE routing and
facade/receipt specs. Acceptance owns RISC-V pair evaluation/patching and its new
spec on `work/item4-riscv-relocations-20261003`. Research owns linker lifecycle
and its new spec on `work/item4-linker-lifecycle-20261003`. Runtime reviews root's
routing and revalidates runtime availability read-only. All use the inherited
model. Root integrates exact commits and reviews source; no runtime PASS or full
item 4 completion is authorized by source review. Remaining source owners are
listed in the acceptance plan rather than relabeled as missing evidence only.

## Full coding continuation ownership (2026-10-03)

Root integrates on `work/item4-full-linker-20261003`, owning hosted FreeBSD,
explicit freestanding file dispatch, publication and documentation. Acceptance
owns RV64 static-driver, ULEB and alignment work in its existing isolated
worktree. Research owns retained spill/file reading and section emission on
`work/item4-linker-bounded-20261003`; it also performs independent integrated
source review. Runtime owns Mach-O static construction and dylib-reading work
in `C:/dev/simple-item4-macho-20261003`, `work/item4-macho-20261003`.

All agents use the inherited model; lower-model sidecars are N/A. Tests are
committed before the corresponding implementation. Root reviews agent source;
acceptance reviews root's hosted/adapter changes and research reviews integrated
Mach-O/adapter changes. Root is the merge owner. Runtime tests, generated-manual
validation and coverage are UNRUN, so source review cannot award verify PASS.
The prior three-attempt runtime diagnostic cap is unchanged.

## Verification readiness continuation (2026-10-03)

The user requests remaining items be divided into implementation and test work
before Phase 4. The authoritative current breakdown is
`doc/03_plan/compiler/linker/item4_verification_readiness.md`.
Root integrates on `work/item4-verification-readiness-20261003`, owns provider
lifecycle binding and common documents. Research owns retained archive/bounded
execution in its original isolated research worktree. Runtime owns hosted Mach-O
in the Mach-O worktree. Acceptance owns remaining RISC-V work in the acceptance
worktree. All start from release `94a16103a5baeefad8bc7688e70b43b75dcf2914`.
No agent edits another lane. Tests precede implementation, root reviews source,
and an independent inherited-model agent reviews root. Lower-model sidecars N/A.

## Historical main forward-port (before branch reconciliation)

The following note describes the earlier main-only adaptation. The reconciled
tree retains the newer release strict authority and configured-linker owners.

### Main forward-port of release PR #2294 (2026-10-03)

The shared ELF admission and executed-engine fixes landed on `release/1.0` in
`7d16ab11d2227cbe5f29dc998b76a1eff326abbb`. The targeted main forward-port
preserves main's existing admission behavior: main lacks the release-only
strict tool/runtime authority modules, so its typed result wraps the existing
entrypoint directly, and the fallback spec omits that unavailable import/check.
All other production guards and acceptance scenarios are carried forward.
Runtime SSpec, generated-manual, coverage and core/MCP evidence remain unrun;
this forward-port does not change any requirement's verification status.
