# Mission-Critical Infrastructure Hardening V2

This guide covers the selected `C1 + O1 + R2 + M2 + N2` implementation lane.
The release claim is fail-closed and remains incomplete until every selected
requirement has current executable evidence and `$verify` reports PASS.

## Current implementation surfaces

- Compiler admission: `compiler.common.mission_critical.compiler_admission`
  accepts only a versioned collector receipt bound to exact run/source/config/
  toolchain/dependency/environment/input-bundle hashes, resolved executable,
  pure-Simple parent lineage, and the complete ordered discriminating-fixture
  set. Rust seed, hybrid, stale, unknown, incomplete, duplicate, malformed, or
  mismatched evidence is rejected.
- SimpleOS manifest: `os.sosix.mission_critical.certified_manifest` requires the
  exact canonical four-host × six-guest catalog. A fully evidenced selected subset may pass only its
  scoped certification; `umbrella_all_platforms` remains false unless all 24
  cells pass. Guest evidence must be target-side and correlated to the same
  run/source/image/configuration.
- Rendering: `common.mission_critical.draw_ir_generation_arena_v3` binds a
  count/byte plan to one arena, generation, and packed layout, recomputes caller
  totals, admits before mutation, seals only exact use, and requires explicit
  abort after mismatch. Active-generation growth and generation wrap are refused.
- Allocation: `nogc_sync_mut.mission_critical.domain_arena_v1` permits sealed,
  per-domain, quota-bounded transactions only in approved noncritical contexts.
  Kernel, ISR, storage commit, ownership publication, isolation transition,
  unsealed, stale-generation, and quota failures reject without publication.
- Process policy: `nogc_sync_mut.mission_critical.bounded_process_policy`
  validates fixed worker/queue/capture bounds and rejects `pid <= 0` before an
  owner process facade may signal or wait.

These modules validate/admit evidence and bounded state; they do not fabricate
host, compiler, GPU, RenderDoc, stress, or external-platform evidence.

## Operator flow

1. Resolve the existing conflict in
   `src/compiler/70.backend/backend/runtime_compiler.spl` under its owning
   session. Until then, every Simple spec is blocked at `TripleLt` parsing.
2. Build and deploy an exact-current pure-Simple compiler; do not use the Rust
   seed or a hybrid artifact as production evidence.
3. Refresh the nine stale reports named by the retained baseline
   `/tmp/simpleos-hardening-v2-baseline.out` through their canonical owner gates.
4. Execute focused admission specs once, then the planned lane gates once.
5. Collect real selected-host SimpleOS and rendering provenance; unavailable
   rows remain visible blockers to broader claims.
6. Run the final aggregate and `$verify`; do not release from source inspection
   or static receipts alone.

### Unified aggregate admission

`scripts/check/check-mci-v2-aggregate.shs` is the host-independent REQ-MCI-002/
REQ-MCI-010 collector. It does not rerun lane gates. Put one canonical receipt
per fixed owner at `<evidence>/receipts/<check-id>.receipt`. Tooling has one
`tooling.receipt`; its library/MCP/LSP/bootstrap/lint/duplication/whole-test/
perf/runtime-contract/direct-env rows belong inside its artifact, not as
redundant aggregate rows. Then invoke:

```sh
sh scripts/check/check-mci-v2-aggregate.shs \
  --evidence build/evidence/mci-v2 \
  --run-id "$RUN_ID" --source-hash "$SOURCE_SHA256" \
  --configuration-hash "$CONFIGURATION_SHA256" --now-utc-ns "$NOW_UTC_NS" \
  --trusted-key "$TRUSTED_PUBLIC_KEY_PEM" --trusted-key-id "$TRUSTED_KEY_ID"
```

Receipt lines are canonical and ordered: `receipt_schema` (exactly
`mci-lane-receipt-v1`), `check_id`, the row-specific `producer_class`,
`attestation` (exactly `signed-v1`), pinned `trusted_key_id`, safe
`signature_relpath`, `run_id`, `source_hash`, `configuration_hash`,
`captured_at_utc_ns`, `valid_until_utc_ns`, `result`, `scenarios`, the safe
basename `artifact_relpath`, `artifact_sha256`, then `receipt_hash` (the SHA-256
of all preceding lines including newlines). Capture age and receipt lifetime
must each be at most 86,400 seconds. Receipt and artifact must be regular,
non-symlink files beneath the evidence tree and remain identical while copied
to the collector's private snapshot directory. The snapshotted artifact is
re-hashed at admission. Missing, unknown/duplicate/noncanonical fields, stale,
skipped, failed/blocked, synthetic/untrusted producer, wrong-run/source/config,
unsafe path/type, scenario-map mismatch, and bad artifact or receipt hashes
remain `BLOCKED`.

The operator must pass `--trusted-key <public.pem> --trusted-key-id <id>`.
OpenSSL verification covers the exact canonical receipt, including its artifact
hash. A self-asserted producer class, missing trust root, wrong key ID, missing
signature, or signature from any other key cannot admit a row.

The deterministic `aggregate-report-v1.env` preserves fixed check order. The
shell contract `test/01_unit/scripts/mci_v2_aggregate_contract_test.shs` owns
`MCI-AGG-001/002/003`; its `collector_contract=PASS` proves collector mechanics
only. The release-facing `result` remains `BLOCKED` while any real owner receipt
is absent or invalid. The report prints a resume command for each blocked row only when that exact
owner script exists and is executable. Otherwise it prints a `BLOCKED
prerequisite`, never a speculative command. Publication uses a private
same-directory temporary generation, sync, atomic rename, and post-rename hash
verification.

### Process-safety producer

`scripts/check/check-mci-v2-process-safety.shs` compiles and executes the strict
C owned-process runtime selfcheck plus its ABI adapter and non-Unix fail-closed
selfchecks under fixed time and capture bounds. It records hashes for the C ABI,
the Simple process facade, and every compiler/runtime symbol-closure owner.

The focused Simple policy/facade specs run only when `--simple-runner` is paired
with a regular, executable runner and `--runner-admission` contains exactly one
`mci-simple-runner-admission-v1` binding for its SHA-256, the requested source
hash, configuration hash, `authority=exact-current-pure-simple`, and
`result=pass`. Without that admission the command exits `2`, retains a
deterministic diagnostic artifact, and reports `release_candidate=false`.

Even a successful producer does not self-attest. It writes
`receipts/process-safety.receipt.template`, never a `.receipt` or signature.
The independent producer-key operator must review the artifact, preserve the
canonical template bytes through `receipt_hash`, publish them as
`process-safety.receipt`, and create the detached `process-safety.sig`. Until
then the aggregate correctly reports the row missing. The fixture contract is
`test/01_unit/scripts/mci_v2_process_safety_contract_test.shs`; its copied local
runner and unsigned output prove classification mechanics only, not release
admission.
Resume commands are instructions only: the collector never starts hardware,
QEMU, stress, rendering, or subordinate tooling. Therefore unavailable rows
remain visibly blocked until their canonical receipts are supplied.

The reviewer row is deliberately separate from traceability. Pass
`--reviewer-key` and `--reviewer-key-id` as a trust root distinct from the lane
producer key and ID. The reviewer decision canonically binds identity,
`independent-release-reviewer` role, `mci-v2-aggregate` scope, run, source,
configuration, decision/expiry times, approval, and the emitted pre-review
`aggregate_candidate_sha256`. The candidate is the canonical evidence graph:
policy/header, ordered checks, canonical/raw receipt and signature digests,
declared/verified artifact digests, blocker/resume ownership, and unexpected
receipt membership. Valid evidence replacement or unexpected-set changes
therefore require review again. Missing, stale, replayed, malformed, same-key, or
self-issued decisions fail closed. This verifier is executable; producing a
real receipt still requires an independently administered reviewer outside the
release requester, traceability gate, and collector. The focused test creates
ephemeral distinct keys and makes no real-review claim.

## Canonical design and traceability

Run the host-independent traceability producer before aggregate admission. It
checks the canonical SSpec/manual pair, feature and NFR requirements,
architecture, detail design, guide, and system-test plan; requires the frozen
20-requirement and 51-scenario sets and their exact requirement-to-scenario
tuples; rejects source-provenance/manual-path/layout, duplicate/embedded-ID,
symlink, and placeholder defects; and emits `artifacts/traceability-v1.env`
plus `receipts/traceability.unsigned-receipt` only after consuming a real
docgen-produced provenance receipt alongside the manual, binding the docgen
tool version, exact command, SSpec hash, and manual hash. Missing provenance or
the present incomplete 51-scenario annotations/rows leaves the producer
**BLOCKED**; source text cannot self-declare freshness. The latter is deliberately an
`unsigned-v1` template, not an aggregate-admissible receipt. The producer never
holds a private key and does not perform reviewer work:

```sh
sh scripts/check/check-mci-v2-traceability.shs \
  --evidence build/evidence/mci-v2 --run-id "$RUN_ID" \
  --source-hash "$SOURCE_SHA256" --configuration-hash "$CONFIGURATION_SHA256" \
  --captured-at-utc-ns "$CAPTURED_NS" --valid-until-utc-ns "$VALID_UNTIL_NS" \
  --trusted-key-id "$TRUSTED_KEY_ID"
```

After independently verifying the artifact and template, the producer-key
operator must convert `receipt_template_schema=mci-lane-unsigned-template-v1`
to `receipt_schema=mci-lane-receipt-v1`, convert `attestation=unsigned-v1` to
`attestation=signed-v1`, append `receipt_hash` over those canonical lines, sign
those same pre-hash canonical bytes, and atomically publish both
`receipts/traceability.receipt` and `signatures/traceability.sig` from private
same-directory temporary files. The aggregate must remain blocked until both
published outputs re-hash and the detached signature verifies. The private key
path is an operator input to that external workflow, never producer state.
`test/01_unit/scripts/mci_v2_traceability_contract_test.shs` covers missing
canonical input, source-provenance/manual-source mismatch, placeholder,
scenario drift/duplication, outside paths, symlink parents, and unsigned output.

- Requirements: `doc/02_requirements/feature/mission_critical_infra_hardening_v2.md`
- NFRs: `doc/02_requirements/nfr/mission_critical_infra_hardening_v2.md`
- Architecture: `doc/04_architecture/mission_critical_infra_hardening_v2.md`
- Detail design: `doc/05_design/mission_critical_infra_hardening_v2.md`
- System-test plan: `doc/03_plan/sys_test/mission_critical_infra_hardening_v2.md`
- Parallel ownership: `doc/03_plan/agent_tasks/mission_critical_infra_hardening_v2.md`
