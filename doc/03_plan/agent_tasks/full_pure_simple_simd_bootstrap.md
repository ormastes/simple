# Full Pure-Simple SIMD Bootstrap Agent Plan

Status: Active

Requirements: `doc/02_requirements/feature/full_pure_simple_simd_bootstrap.md` and `doc/02_requirements/nfr/full_pure_simple_simd_bootstrap.md`.

## Shared contracts

- Public SIMD facade: one platform-neutral API with explicit scalar fallback.
- Backend identity: stable scalar/SSE2/SSSE3/SSE4.1/AVX/AVX2/AVX-512/NEON/SVE/SVE2/RVV/SIMD128 names.
- Phase receipt: compiler and launched artifact paths/SHA-256, provenance, producing phase, supported commands, plugin version/tree hash, exact argv, protocol/read assertion, result, duration, bounded sanitized evidence, owner, prerequisite, and exact resume command. A suite PASS does not imply a launch or provider-access PASS.
- SSpec steps use concrete setup/action/check names and fail fast with `assert(false)` until implemented; placeholder passes are forbidden.

## Work lanes

1. **Compiler and backend lane**: finish fixed-width and scalable-vector lowering, legality checks, masks/tails, capability dispatch, and interpreter parity. Owner: compiler lane. Reviewer: merge owner.
2. **Library and runtime lane**: expose pure-Simple portable SIMD operations, scalar fallbacks, capability cache, and forced-backend test control. Owner: runtime/library lane. Reviewer: merge owner.
3. **Database and web lane**: select representative scan/filter and HTTP classify/parse kernels, integrate through the shared facade, and retain correctness plus performance fixtures. Owner: DB/web lane. Reviewer: merge owner.
4. **Bootstrap and deployment lane**: repair the trusted four-stage bootstrap, admit Stage 4, build cached Simple/MCP/LSP MCP artifacts, deploy with rollback receipts, and prohibit Rust-seed/raw-source release evidence. Owner: bootstrap lane. Reviewer: merge owner.
5. **Phase verification lane (additional task)**: for every admitted compiler/interpreter phase, launch all supported artifacts and run their tests; explicitly verify MCP, Simple LSP MCP, the pinned SPipe plugin/SSpec runner, DevHub, and LLM Caret. DevHub must prove GitHub, Jira, and Confluence authenticated read access in three independent rows. Record unsupported/unconfigured commands as fail-closed rows with exact resume steps. Owner: verification lane. Reviewer: final verifier.
6. **Documentation and architecture lane**: refresh SIMD research, architecture, detailed design, system-test plan, executable specs, generated manuals, and operator guides. Owner: documentation lane. Reviewer: merge owner.
7. **Performance lane**: lock fixtures and qualified hosts, measure selected backend identity, correctness, p50/p95/p99, throughput, and max RSS, and prove Profile 2 thresholds. Owner: performance lane. Reviewer: final verifier.

## Sequence and gates

1. Freeze shared APIs, backend names, benchmark fixtures, SSpec helpers, and receipt schema.
2. Complete architecture and detailed design before accepting parallel implementation output.
3. Merge compiler/runtime foundations, then DB/web integrations and phase verification tooling.
4. At each phase freeze the artifact identity, build its permitted companion tools in separate caches, actually launch them, run the applicable component suites, and retain every blocked/unsupported row before constructing the next phase. Build and admit the exact Stage 4 CLI; run the essential-tools smoke once.
5. Build, deploy, and smoke Simple MCP and Simple LSP MCP from cached native artifacts.
6. Run the phase verification matrix and full release-bound SPipe suite once per unchanged candidate.
7. Run production verification, require `STATUS: PASS`, isolate selected files, commit, rebase linearly, and push.

## Completion evidence

- Cross-target correctness and unsupported-capability receipts.
- Aggressive Profile 2 benchmark report.
- Four-stage bootstrap and essential-tools receipts.
- Compiler/interpreter plus MCP/SPipe/DevHub/Caret phase matrix.
- Deployment and rollback receipts for Simple, MCP, and LSP MCP.
- Final requirement-to-evidence matrix and independent final review.

Merge owner: primary Codex session. Final reviewer: independent highest-capability reviewer after all lane outputs are integrated.

## Per-phase actual-launch work, added 2026-09-08

Requested model for the repair/review lane: Astra. The prior no-progress reports
are not verification. The new scoped repair first records focused resolver
evidence; the bootstrap owner then makes one changed-candidate attempt while
preserving existing caches and live process ownership.

Every phase below must materialize the same row set. A missing capability is
visible as `UNSUPPORTED`; missing artifact/admission/auth/configuration is
`BLOCKED`; an executed bad response is `FAIL`. None earns PASS. Building a later
compiler may proceed when its own compiler handoff is admitted, but this cannot
close an earlier phase's tool coverage or the feature's complete phase matrix.

| Phase | Required launch and suite work | Admission and retained blockers |
|---|---|---|
| 0: host preflight | Resolve and launch the exact Rust/C/link tools; verify host prerequisite versions and supported target before expensive builds. Inspect plugin checkout/config paths without exposing credentials. | Record host/target/tool identities and the focused authority receipt. This preflight is not a product live-check PASS. |
| 1: admitted seed generation | Execute receipt-admitted bootstrap sanity. Build/launch only explicitly permitted pure-Simple companion closures for compiler/interpreter, MCP/LSP, SPipe plugin, Caret, and DevHub; execute all supported suites and the three DevHub provider reads. | Seed itself remains bootstrap-only. Missing pure-Simple companions produce explicit rows for each affected tool/provider. No raw-source product substitute. |
| 2: receiver | Launch exact receiver; compile/run the frozen semantic fixture and compare output. Build same-producer companions when admitted, then launch MCP/LSP, SPipe plugin, Caret, DevHub and provider reads; execute every phase-supported suite. | Compiler-only receipt does not confer general `test`/SPipe authority. Missing full CLI or test runner remains blocked, with phase-2 producer cache and resume instructions retained. |
| 3: self-hosted compiler | Verify its parent receipt, then launch compiler/interpreter and the admitted phase-3 companions. Run the same MCP/LSP, plugin, Caret, DevHub, GitHub/Jira/Confluence checks and all supported suites. | No phase-4 binary or deployed wrapper may supply phase-3 evidence. Companion entry closures and isolated caches bind the phase-3 producer SHA-256. |
| 4: full CLI candidate | Launch exact full CLI/interpreter, native MCP/LSP, pinned SPipe plugin, Caret, DevHub; execute all live sanity rows plus complete applicable suites and release-bound `test test --whole --mode=interpreter`. | Every required row must pass. Missing credentials, target read permission, or plugin admission blocks acceptance; fixture tests of the gate do not replace live evidence. |
| 5: deployment | Transactionally install the verified CLI/MCP/LSP artifacts, launch canonical wrappers, resolve their actual target hashes, and rerun deployment-specific MCP/LSP protocol and integration entrypoints against the deployed identities. | Record wrapper-to-artifact mapping, rollback proof, launch timing and RSS. Unchanged pre-deployment unit suites are reused by fingerprint, not repeated. |

## Mandatory row assertions

| Row family, repeated in phases 1–4 | Actual check and required evidence |
|---|---|
| Compiler/interpreter | Exact binary startup plus a compile-and-execute semantic fixture with expected output; interpreter behavior only through declared supported mode. Freeze full applicable unit/integration/system/doctest inventory. |
| MCP and LSP MCP | Spawn each exact cached server, complete JSON-RPC `initialize`, send `notifications/initialized`, validate nonempty `tools/list`, and invoke a declared read-only workspace/language tool against a known fixture. Match IDs, success result schema, and expected fixture identity; retain clean shutdown/timeout status. |
| SPipe plugin | Validate the installed plugin manifest/version and pinned checkout/tree; launch its real CLI/plugin command using the phase-bound artifact; execute a nonempty SSpec fixture and doc generation with authenticated runner evidence. A plugin manifest, `--help`, Node sidecar, or directory existence alone proves no phase-bound runtime execution. |
| LLM Caret | Launch the admitted cached Caret entrypoint; exercise local status/room discovery or protocol read in an isolated fixture room, and run the frozen applicable Caret suite. Do not send messages to other users or agents for this sanity row. |
| DevHub | Launch exact cached DevHub and run its applicable suite; discover supported provider/read commands and verify real provider responses. Help is a startup subcheck only. |
| GitHub access | Through that DevHub artifact, perform authenticated current-user/read-capability sanity and read a known repository. Validate expected host and repository identity, not just `gh` installation/auth config. |
| Jira access | Through that DevHub artifact, perform authenticated identity/read-capability sanity and `jira view <fixture-key> --json`. Require the expected issue key/id and a successful non-error JSON result. JQL returning an empty array proves neither fixture access nor complete read scope. |
| Confluence access | Through that DevHub artifact, perform authenticated identity/read-capability sanity and `wiki view <fixture-page-id> --backend confluence --json`. Require the expected page id, title/type, and successful non-error JSON result. Validate the configured tenant/base path. |

`src/app/devhub/cmd_auth.spl` currently returns zero from `auth status` even when
Jira is unconfigured; its Jira indicator checks only whether a URL is set.
Therefore that output is diagnostic metadata, never the acceptance oracle.
Provider identity/capability commands unavailable in a companion are explicit
implementation blockers, not invented command successes.

Use existing credentials through the provider's credential owner; never copy
tokens into argv, manifests, logs, repository config, or receipts. Logs retain
bounded sanitized assertions and response hashes, not issue/page body content.
Missing credentials or fixture IDs must produce an exact required-config key and
a rerun command with placeholders for nonsecret IDs; no external write or login
mutation is part of these checks.

## Resume and evidence ownership

For each row record `phase`, `row_id`, `required_capability`, `status`, `reason`,
`owner`, `reviewer`, `prerequisite`, `resume_command`, compiler/artifact and
provenance paths/hashes, source/input inventory hash, plugin manifest/tree hash,
protocol/tool/read assertion, sanitized endpoint/provider/fixture identity,
credential-source label (never the credential), exact command argv hash, isolated
cache/output/home/tmp roots, start/duration/timeout/exit, and retained log and
receipt paths/hashes. Capture before/after identities and reject drift.

Owner: bootstrap lane for phase admission/companion construction; verification
lane for actual launch and suites; DevHub lane for provider configuration/read
capability. Reviewer: Astra final verifier. The detailed executable command
contract belongs in the trusted deployment matrix and must match its harness.
Every blocked row remains in the feature's requirement trace until its live
check passes; compiler construction progress never silently closes it.
