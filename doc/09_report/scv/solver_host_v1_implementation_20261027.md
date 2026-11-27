# Solver host V1 implementation lane

Owner: Codex `/root/impl_solver_host`, session 2026-10-27.
Base: `25cdeee5d5da8f8c7c3ab530d43bc2fd4a360d26`.
Worktree: `/tmp/simple-scv-impl-host-20261027`.
Branch: `work/scv-impl-host-20261027`.
Target: SCVN-P01/P03/P04/P05 local vertical source and DB proposal integration.

Uses the implementation and coding skills and approved full-phase2 architecture/detail design. Owns new contract, host, pure source/DB adapter, fixture/spec, and this report only. Existing store, merge, file buffer, CLI, compiler, schema, configuration and snapshot modules belong to other lanes.

Runtime evidence is unavailable: no admitted runtime was found by the runtime lane. No Simple check/test/docgen, seed, bootstrap, publication, push, PR or merge is authorized in this worker lane. Source review is not execution qualification.

Implemented source: fixed built-in descriptor contracts; separate trusted accepted bindings; exact raw-byte and evidenced-move draft merge; distinct copy IDs; typed schema V2 and existing row reducer adapters; host-owned mandatory exact-subject checks; conservative disjoint plan composition; all-input pre-serialization resource accounting. Authored source/schema/rows specs and manual mirrors use production owners.

Review corrected two priority findings: metadata and nested values now consume budget before any encoding/hash, including accepted configuration; matching arbitrary provider labels no longer imply the identity of the executing artifact. All computed drafts/conflicts report `needs_inputs`/`unqualified-builtin-execution`; no public receipt constructor, qualified proposal or reusable result key exists. Actual checked input bindings remain separately inspectable.

Open mandatory work: admitted runtime and execution; actual provider loader/artifact/ABI admission; parser/model semantic profiles; external receipt verification; bounded native heap/sandbox execution; admitted result cache; durable conflict store and guarded resolution reuse; full combined-candidate validation and publisher integration. SCVN-P01/P03/P04/P05 are partial source integration, not completed tasks. Native SPipe/docgen/sspec-maintain, coverage and core/MCP smoke checks have not run.

One static verification pass: staged whitespace check passed; direct-env-runtime-guard `--working` and `--staged` each returned `STATUS: PASS`; executable-spec layout count under `doc/06_spec` was `0`. These are not a production-readiness PASS or runtime evidence.
