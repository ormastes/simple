# Mission-Critical Infrastructure Hardening V2

This guide covers the selected `C1 + O1 + R2 + M2 + N2` implementation lane.
The release claim is fail-closed and remains incomplete until every selected
requirement has current executable evidence and `$verify` reports PASS.

## Current implementation surfaces

- Compiler admission: the host-independent producer
  `scripts/check/check-mci-v2-compiler-admission.shs` validates the single fixed
  `MCI-COMP-001` fixture against an authenticated exact-current pure-Simple
  compiler lineage. It does not implement the independent two-build,
  mutation-campaign, or reproducibility scenarios. `MCI-COMP-002/003` and
  `MCI-NFR-003/004` remain explicit release blockers.
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

The canonical release entrypoint is `scripts/check/check-mci-v2-release.shs`.
It requires externally provisioned producer/reviewer keys and decision inputs;
it never generates a key. Live lane arguments are supplied through
`MCI_<LANE>_ARGS_FILE` files containing one whitespace-free argument per line;
the runner verifies the common evidence root, run, source, and configuration
values before invoking the fixed canonical producer executable. It then uses
`sign-mci-v2-lane.shs`, requires the first aggregate to block pending review,
activates the independent reviewer generation, and runs one final aggregate.
The evidence directory must be fresh and canonically below the repository;
dot-segment traversal and collisions fail before publication. The orchestrator
pins the evidence directory identity across every child and accepts live argv
files only as unique option/value pairs whose common identity values are
adjacent and exact. Children have a fixed timeout, per-stream capture ceiling,
and memory/process ceilings through `prlimit` or supported BSD/macOS shell
limits. Captures and aggregate publications are atomic no-replace outputs.
Candidate and final aggregate reports use distinct paths, preserving the
candidate bytes reviewed in pass one; the final report is also published under
the compatibility name `aggregate-report-v1.env`. Artifact bytes, tooling
archive members, and expanded tooling bytes are capped before admission. The live compiler
producer's independent cross-host prerequisite remains an explicit BLOCKED and
prevents signing when it cannot produce an unsigned template. `--contract-fixture` is only
for the focused shell contract and always reports `CONTRACT_ONLY`, never PASS.

1. Resume the Stage 3 self-host crash from the exact evidence and fresh-session
   command in
   `doc/08_tracking/bug/stage3_selfhost_exit_139_2026-08-14.md`. The old
   `runtime_compiler.spl`/`TripleLt` conflict is resolved and is not the current
   blocker. The last bounded cycle built and sanity-checked Stage 2, then
   `stage3-native-build` exited 139.
2. Build and admit an exact-current Stage 4 pure-Simple compiler; do not use the Rust
   seed or a hybrid artifact as production evidence.
3. Refresh the nine stale reports named by the authoritative retained baseline
   `/tmp/mci-v2-hardening-matrix-20260811.log` (SHA-256
   `cd982a1142beb3cc1a51eb022d7a0d1eb4b849f265813c4a68d51b681280eb38`)
   through their canonical owner gates. The distinct
   `/tmp/simpleos-hardening-v2-baseline.out` is a derived diagnostic, not the
   canonical baseline.
4. Execute focused admission specs once, then the planned lane gates once.
5. Collect real selected-host SimpleOS and rendering provenance; unavailable
   rows remain visible blockers to broader claims.
6. Run the final aggregate and `$verify`; do not release from source inspection
   or static receipts alone.

The authoritative status/acceptance/blocker ledger is
`doc/03_plan/sys_test/mission_critical_infra_hardening_v2.md`. Parallel work is
owned by `doc/03_plan/agent_tasks/mission_critical_infra_hardening_v2.md`; phase
history is `.spipe/mission_critical_infra_hardening_v2/state.md`. Reusable
knowledge is linked from the mission-critical V2 feature expert and the
compiler-driver, mission-critical-memory, and UI-render layer experts under
`doc/00_llm_process/`.

### Compiler admission producer

The producer derives the ordered tracked-file set for `src/compiler`,
`src/app`, and `src/lib`, copies every regular file into a private build
snapshot while checking its identity and digest, and then re-derives the live
manifest. A file-set or digest change during capture fails closed. Compilation
uses only the private snapshot through absolute `--source` paths and a
snapshot-local `SIMPLE_LIB`, so later worktree changes cannot create a
manifest/build TOCTOU mismatch. The fixture, compiler, provenance, signatures,
and trust keys are independently snapshotted too.

Passing fixture mode proves only the `MCI-COMP-001` producer contract and emits
`CONTRACT_ONLY`. Live mode can prove `MCI-COMP-001` only after trust policy is
provisioned, and still exits blocked with `release_candidate=false` because
`MCI-COMP-002`, `MCI-COMP-003`, `MCI-NFR-003`, and `MCI-NFR-004` have no
executed evidence. No compiler lane receipt is published from this incomplete
producer.

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
is absent or invalid. The report prints a resume command for each blocked row
only when that exact owner script exists and is executable and every
producer-required argument has an explicit, non-empty `MCI_*` environment
prerequisite. Compiler, tooling, SimpleOS, rendering,
allocation/fault-injection, process-safety, and traceability all receive the
same aggregate `--evidence "$MCI_EVIDENCE"` root; lane-owned artifact names
provide separation. Missing mappings produce `BLOCKED prerequisite: set
required resume environment: ...`, never an incomplete command. The static
`mci_v2_resume_command_contract_test.shs` checks executable ownership, usage
flags, common-root routing, and environment gating. Publication uses a private
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

The allocation producer executes the canonical `DomainArenaV1` ledger once but
publishes two independently signable lanes. `allocation.unsigned.template`
binds the allocation/quota subset (`MCI-ALLOC-001..005`, `MCI-NFR-007/008`) to
`mci-allocation-domain-arena-evidence-v1`;
`fault-injection.unsigned.template` binds the injection/isolation subset
(`MCI-ALLOC-006`, `MCI-NFR-009/010`) to
`mci-fault-injection-domain-arena-evidence-v1`. Controlled fixtures remain
`artifact_mode=fixture`, `release_eligible=false`; changing those fields after
signing invalidates the detached signature and cannot promote fixture evidence.

### SimpleOS schema-2 manifest producer

`scripts/check/check-mci-v2-simpleos-manifest.shs` consumes an ordered
`certified-platform-manifest-v2` file containing exactly the canonical 24 rows
(`linux`, `windows`, `macos`, `freebsd` × `x86_32`, `x86_64`, `arm32`, `arm64`,
`riscv32`, `riscv64`). Each `row=` is pipe-delimited as
`cell|selected|reason|host_identity|guest_identity|configuration_hash|image_hash|collector_receipt_relpath|collector_signature_relpath`.
Unselected rows require a reason and no receipt paths. Selected rows require a
trusted `simpleos-qemu-host-collector-v1` receipt correlated to the exact cell,
run, source, compiler receipt, configuration, and image. The producer derives
the aggregate configuration identity from the snapshotted
`--configuration-manifest`; every visible row must carry that same digest.

Live admission additionally requires a detached signature from the configured
collector trust root, `attestation=signed-real-v1`, a real QEMU/host collector,
target-side execution from guest filesystem storage, hashes for `/usr/bin`,
`/bin`, `/sys/apps`, and `/SYS/SIMPLETOOL.SDN`, an exact 24-hour stress receipt,
and evidence freshness/lifetime no greater than 24 hours relative to the
decimal-safe `--now-utc-ns` admission time. Payload evidence includes hashed
version, compile, and run commands, zero exit statuses, and snapshotted
schema-tagged transcript artifacts plus a schema-tagged alias-identity artifact.
Stress evidence includes exact start/end times, snapshotted schema-tagged
resource-series and invariant-ledger artifacts, and zero invariant violations.
Every selected collector uses exactly the lane template's capture and expiry
times; a merely overlapping collector interval is rejected.
Missing, synthetic,
unsigned, stale, mismatched, symlinked, or incomplete evidence remains
`BLOCKED`. `--contract-fixture` exercises these classifications but can never
produce live PASS.

The producer rejects symlinks in every input ancestor, snapshots inputs, and
publishes through the shared `openat`/`O_NOFOLLOW`, fsyncing,
atomic-no-replace helper,
and emits `artifacts/simpleos.evidence` plus
`receipts/simpleos.receipt.unsigned.template`. It never creates the aggregate-
admissible `.receipt` or signature. An independent producer-key operator must
review the evidence, convert the template to the canonical signed lane receipt,
and publish the detached signature. The focused fixture contract is
`test/01_unit/scripts/mci_v2_simpleos_manifest_contract_test.shs`; it does not
run QEMU or claim platform certification.

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
plus `receipts/traceability.unsigned.template` only after consuming a real
docgen-produced provenance receipt alongside the manual, binding the docgen
tool version, exact command, SSpec hash, and manual hash. Missing provenance
leaves the producer **BLOCKED**; source text cannot self-declare freshness.
`MCI-DOC-001/002` remain explicitly blocked and are not claimed by the
template; only the focused negative-control scenario `MCI-DOC-003` is bound.
The template is canonical lane-receipt-shaped but is not aggregate-admissible
until its signer placeholders and hash are replaced and a detached signature
is published. The producer never
holds a private key and does not perform reviewer work:

```sh
sh scripts/check/check-mci-v2-traceability.shs \
  --evidence build/evidence/mci-v2 --run-id "$RUN_ID" \
  --source-hash "$SOURCE_SHA256" --configuration-hash "$CONFIGURATION_SHA256" \
  --captured-at-utc-ns "$CAPTURED_NS" --valid-until-utc-ns "$VALID_UNTIL_NS" \
  --trusted-key-id "$TRUSTED_KEY_ID"
```

After independently verifying the artifact and template, the producer-key
operator must replace `attestation=EXTERNAL_SIGNER_SETS_signed-v1` with
`attestation=signed-v1`, set the reviewed producer key ID and signature path,
replace the receipt-hash placeholder with SHA-256 over the canonical pre-hash
lines, sign
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
