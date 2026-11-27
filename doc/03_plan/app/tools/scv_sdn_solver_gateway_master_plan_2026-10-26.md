# SCV Consolidated Implementation Plan
## SDN configuration, domain-specific solver plugins, syntax-aligned storage, and a hybrid Git gateway

**Date:** 2026-10-26  
**Document revision:** 2.0 — planning revision, not a claim about the SCV release or on-disk format version  
**Repository:** `ormastes/simple`  
**Targeted source-audit revision:** `684af83fa9818aa5bfde83e065372bf204c9e651`  
**Suggested repository destination:** `doc/03_plan/app/tools/scv_sdn_solver_gateway_master_plan_2026-10-26.md`  
**Replaces:** conflicting recommendations in the 2026-10-16 master plan and the subsequent discussion. Retains its byte-preservation, syntax-storage, hash-conformance, migration, recovery, and evaluation requirements.  
**Status:** Proposed architecture and implementation backlog. No repository changes, SCV test execution, native SDN example execution, or performance measurements were performed for this document.

> **Primary decision:** Use **SDN for every native configuration, policy, plugin manifest, lockfile, schema declaration, and human-readable protocol**. Source code, configuration, database schema, and database values share an infrastructure layer, but **must not share one generic conflict-resolution rule**. Install versioned domain-specific solvers in the same manner that parser providers and grammar packs are installed. A parser describes structure; a solver proposes a result; validators check it; the publication authority decides whether it can be accepted.

The plan preserves local work even when parsing, solving, compiling, or settlement fails. It reduces avoidable conflicts without concealing real conflicts, and bounds computation, metadata, and retained history without deleting acknowledged work.

## Contents

1. [Decisions and requirement traceability](#1-decisions-and-requirement-traceability)
2. [Refreshed implementation audit](#2-refreshed-implementation-audit)
3. [Target topology and authority model](#3-target-topology-and-authority-model)
4. [Save, checkpoint, validation, build, and commit lifecycle](#4-save-checkpoint-validation-build-and-commit-lifecycle)
5. [SDN-only configuration and policy contracts](#5-sdn-only-configuration-and-policy-contracts)
6. [Parser, domain model, solver, validator, and publisher plugins](#6-parser-domain-model-solver-validator-and-publisher-plugins)
7. [Deterministic routing and solver composition](#7-deterministic-routing-and-solver-composition)
8. [Source-code solver family](#8-source-code-solver-family)
9. [Textual database schema solver](#9-textual-database-schema-solver)
10. [Textual database row and value solvers](#10-textual-database-row-and-value-solvers)
11. [Stable identities, clocks, compact aliases, and settlement](#11-stable-identities-clocks-compact-aliases-and-settlement)
12. [SDN configuration solver](#12-sdn-configuration-solver)
13. [Conflict objects, resolution receipts, and reuse](#13-conflict-objects-resolution-receipts-and-reuse)
14. [OS, shell, IDE, and LLM operation capture](#14-os-shell-ide-and-llm-operation-capture)
15. [Configurable multi-hash infrastructure](#15-configurable-multi-hash-infrastructure)
16. [Structural storage, compression, and exact reconstruction](#16-structural-storage-compression-and-exact-reconstruction)
17. [Bounded growth, durability, scheduling, and cache reuse](#17-bounded-growth-durability-scheduling-and-cache-reuse)
18. [Native SCV gateway and Git/GitHub publication](#18-native-scv-gateway-and-gitgithub-publication)
19. [Compiler, build/test runner, context retrieval, and agents](#19-compiler-buildtest-runner-context-retrieval-and-agents)
20. [Module ownership and integration plan](#20-module-ownership-and-integration-plan)
21. [Implementation backlog](#21-implementation-backlog)
22. [Parallel delivery waves and prior-plan crosswalk](#22-parallel-delivery-waves-and-prior-plan-crosswalk)
23. [Acceptance tests and CI](#23-acceptance-tests-and-ci)
24. [Performance and conflict-reduction evaluation](#24-performance-and-conflict-reduction-evaluation)
25. [Migration, recovery, and rollout](#25-migration-recovery-and-rollout)
26. [Risk register and completion criteria](#26-risk-register-and-completion-criteria)
27. [Research and source references](#27-research-and-source-references)

---

## 1. Decisions and requirement traceability

### 1.1 Consolidated decisions

| ID | Requirement | Implementation direction |
|---|---|---|
| R01 | Native configuration must be SDN | No YAML/JSON/TOML alternative for native SCV configuration. Foreign APIs retain boundary adapters. |
| R02 | Source and database conflicts differ | Separate source, DB schema, DB value, configuration, and opaque-content solver contracts. |
| R03 | Solvers are replaceable plugins | Versioned capabilities, pinned artifacts, SDN profiles, bounded execution, explicit fallback policy. |
| R04 | Tree-sitter/native parsing remains central | Reuse CST, byte spans, edits, and source identities; parsing alone grants no merge or publication authority. |
| R05 | Source compression is syntax aligned | Complete nodes, blocks, and sibling sequences; no arbitrary byte/token/CDC boundaries for new parsed-source storage. |
| R06 | Hash algorithms are configurable and can coexist | Purpose-typed XXH3, GXHash, BLAKE3, legacy secure providers; compute only the required set. |
| R07 | Preserve invalid local work | Ordinary saves/private checkpoints cannot be rejected merely for syntax errors. Gate verified promotion and automatic build selection. |
| R08 | Capture explicit edit intent | Simple OS operations, host command wrappers, IDE transactions, and agent-tool receipts; validate against effects. |
| R09 | Reduce false conflicts safely | Stable revision-aware identities, typed operations, structured merge, replayable resolution evidence, no false success claims. |
| R10 | Avoid data and CPU explosions | Coalesced transactions, immutable sharing, compact references, checkpoints, bounded caches, conditional retention. |
| R11 | Concurrent DB column additions must work | Stable ColumnUid, immutable schema revisions, typed migration operations, constraints, lazy defaults. |
| R12 | Offline IDs become compact at settlement | Permanent provisional identity plus gateway-authorized, epoch-qualified numeric aliases; timestamps are not identity. |
| R13 | Scion-style services plus distributed autonomy | Thin, hybrid, and full-replica modes over the same core and object model. |
| R14 | Internal hosts can use only SCV | Native SCV protocol to a durable gateway; Git conversion and GitHub integration at the boundary. |
| R15 | Keep Git/jj compatibility and recovery | Existing migration gates continue; do not infer native-authority readiness from a feature implementation. |
| R16 | LLM/build integration shares infrastructure | Exact snapshots, shared parsing/indexing, selective context, compiler-confirmed dependencies, immutable evidence. |

### 1.2 Invariants

**I01 — Byte preservation.** Restoring a retained source or submitted SDN text object returns its original bytes, including invalid syntax, whitespace, comments, encoding, and newlines.

**I02 — Meaning is domain-specific.** A syntactically valid source file may be semantically wrong. A syntactically valid SDN document may violate a schema, constraint, or permission. A valid database merge is not necessarily a valid configuration-policy change.

**I03 — No hidden winner.** Concurrent incompatible scalar values, schema definitions, and source behaviors remain visible conflicts unless an explicit authorized rule resolves them. Timestamp order is not a default winner rule.

**I04 — Identity is not spelling or location.** Source entities, tables, columns, and rows have stable identities independent of path, name, ordinal, alias, and content hash.

**I05 — Plugins cannot authorize themselves.** Solver output never changes the policy that decides whether that output is acceptable. Proposed policy changes use the previously accepted policy.

**I06 — Evidence has an exact subject.** Every proposal, test, schema migration, approval, and settlement receipt binds the exact inputs, output candidate, configuration, and relevant provider versions.

**I07 — Fast hashes are accelerators.** XXH3/GXHash matches require equality confirmation or a trusted secure identity. Secure operations cannot downgrade to noncryptographic hashes.

**I08 — One acceptance authority.** Each protected ref and DB settlement namespace has one logical publication authority and an explicit linearization point.

**I09 — Local durability is not remote acceptance.** Local checkpoint, remote draft durability, upstream publication, and final acceptance are distinct states and acknowledgements.

**I10 — Missing information is not absence or success.** Missing sparse objects, parser artifacts, field mappings, causal dependencies, test results, or indexes produce explicit incomplete/unavailable outcomes.

**I11 — No arbitrary source partition fallback.** Oversized or unparsed regions stay intact opaque units or use an explicitly declared line/document structure; codec buffers are not source identities.

**I12 — Retention follows reachability and promises.** Never evict the sole durable copy of unpublished work, a reconstruction dependency, a necessary alias, or unresolved conflict inputs as though it were a cache entry.

**I13 — Optimization preserves semantics.** Provider/ISA selection cannot change digest semantics; re-encoding cannot change logical source identity; event coalescing cannot erase externally observable operations.

**I14 — Transactions own related changes.** A schema migration and its data/reference changes, or a source refactor and its dependent files, are validated together before atomic publication where the authority supports it.

---

## 2. Refreshed implementation audit

The audit below is a targeted source read at the pinned revision, not a repository-wide runtime certification. Earlier discussion described several already-present DB mechanisms as future work; this plan corrects that and reuses the implementations. [S00]

| Area / inspected file | Observed source | Plan consequence |
|---|---|---|
| `src/compiler_rust/sdn/src/lib.rs` | Documents nested SDN maps, inline arrays using `=`, and named tables. Its `parse_config` entry point explicitly rejects nesting, arrays, and tables. | Use a bounded full-SDN parser plus SCV schema validation, not the restricted flat-config entry point. [S01] |
| `src/lib/common/sdn/strict_types_v1.spl` | Defines strict syntax limits for bytes, depth, nodes, rows, cells, and columns; syntax validation is explicitly separate from schema/trust. | Reuse and verify the real strict parser path; do not infer schema admission from parsing. [S02] |
| `src/lib/scv/distributed_identity.spl` | Has namespace/kind/actor-incarnation/counter UIDs and namespace/epoch/kind/sequence aliases. | Extend the existing identity system to tables and columns; do not introduce a parallel UUID-only identity store. [S03] |
| `db_patch.spl` | Typed row operations, expected values, causal dependencies, schema/reducer revisions, and digest/signature fields. Fields are currently addressed by names in the inspected types; the inspected digest path requires SHA-256 v1. | Add a versioned ColumnUid/schema-operation contract and hash-provider migration; keep existing v1 readers. [S04] |
| `db_reducer.spl` | Pure preview with scalar/list conflict rules, derived fields, observed/remove/add-wins sets, and authority-controlled fields. Preview is not an admission receipt. | Wrap and extend reducers as domain solvers; do not rebuild them as a general source-code merge engine. [S05] |
| `db_schema.spl` | Existing constraints and observed-set add/remove semantics. | Reuse causal dot behavior and constraint checking; add real schema evolution separately. [S06] |
| `db_allocation.spl` | Plans alias allocation after admission checks; preserves original UID internally and projects typed references into settled aliases in one candidate. | Preserve this design; implement/verify the end-to-end accepted-ref receipt and retry path. [S07] |
| `editor_ipc.spl` | Edit/save/rename/refactor events; documented filesystem-spool transport and a TODO for native socket integration. | Complete transport, versioned transaction capture, and real editor/agent callers. [S08] |
| `merge_validation.spl` | Current text-oriented checks reject empty output/NUL and use line balance; compilation/test results are pluggable status inputs. | This is not a universal byte validator. Empty files/binary objects must be valid in the correct domain. Replace protected admission of status strings with verified receipts. [S09] |
| `network_remote.spl` | Header explicitly describes filesystem-backed loopback behavior, auth/resume stubs, and future HTTPS routing. | Real cross-host native service and durable Git gateway remain integration milestones. [S10] |
| `src/lib/common/crypto/blake3.spl` | Current source describes arbitrary-length tree hashing, keyed/KDF/XOF entry points; it no longer describes the earlier 64-byte-only implementation. | **Do not repeat the obsolete 64-byte limitation as a current defect.** Full vector/streaming/provider conformance still requires execution. [S11] |

The 2026-10-16 plan remains evidence for its earlier audit, not proof that its findings still hold. Existing `identity_merge`, parser sessions, native compiler snapshots, sj/jj adapters, paged DB modules, and recovery tooling must receive a refreshed call-graph and execution audit before each integration task is marked done. Neither a source comment nor a filename proves end-to-end behavior.

A unified, policy-bound parser/domain/solver/validator plugin API is a **target in this plan**. The targeted inspection does not establish that such an end-to-end registry already exists or that it is absent from every uninspected module.

---

## 3. Target topology and authority model

### 3.1 One core, several deployment modes

```text
Simple OS / host shell / IDE / LLM tool wrapper
                       |
          operation capture + immutable snapshot
                       |
              SDN policy / routing layer
                       |
       +---------------+-------------------+
       |               |                   |
 source model      SDN DB model       SDN config model
 CST + entities    schema + rows      typed settings
       |               |                   |
 source solvers    schema/data solvers  config solvers
       +---------------+-------------------+
                       |
             proposed candidate + conflicts
                       |
           independent validators / evidence
                       |
        local journal and publication coordinator
                       |
              native SCV replication/API
                       |
               SCV repository gateway
       objects | drafts | indexes | settlement | outbox
                       |
            Git object and forge adapter
                       |
          GitHub / another remote Git server
```

These are components, not a requirement that every save contact a server or execute every plugin.

| Mode | Stored locally | Offline promise |
|---|---|---|
| Thin | Bounded cache and private overlay | Only the advertised cached/pinned scope; no unrestricted history promise. |
| Hybrid — developer default | Durable local revisions and selected source/history closure | Local changes and supported operations within explicitly pinned inputs. |
| Full replica | Complete closure for selected retained refs and native metadata | Independent operation/recovery for that declared scope. |

Client hosts can remain SCV-native. The gateway may initially invoke a pinned Git executable through a binary-safe adapter; implementing Git transport in pure Simple is not a prerequisite for native clients.

### 3.2 Accepted history versus draft storage

Initially, GitHub remains the accepted-history authority for protected refs. The gateway owns durable native shared drafts, rich metadata, and the publication workflow. It may prepare objects and settlement candidates concurrently, but cannot acknowledge `landed` or `settled` before the configured authority accepts and read-back verifies the result.

A later native-authoritative mode can publish to GitHub as a mirror only after the retained cutover gates. Authority is chosen explicitly per namespace/ref, not inferred from which endpoint received a write first.

Local-only and direct Git/jj modes remain supported without an always-on gateway. They use the same typed operations and policy contracts. The new server deployment does not make a dedicated database server mandatory for small repositories.

### 3.3 Scion mechanisms retained, not copied wholesale

Scion's published design uses server-side operations, incremental changesets, separately derived indexes, immutable object requests, cache tiers, and separate ref CAS. Its always-online assumption explains its thin clients; it does not supply an off-the-shelf syntax solver or offline protocol. SCV adopts the incremental/query/cache ideas while retaining local revisions and selective replication. [R01]

No mandatory file locks are required for normal editing. Use isolated workspaces and optimistic integration, with short transactions for protected mutable state. Advisory reservations can warn about overlapping refactors, but cannot replace identity checks or expected-head comparison.

---

## 4. Save, checkpoint, validation, build, and commit lifecycle

### 4.1 Never let syntax gating lose local work

| Action | Invalid syntax/schema allowed? | Required behavior |
|---|---|---|
| Editor buffer / temporary output | Yes | Retain bytes locally; mark unsaved or temporary. |
| Ordinary filesystem save | Yes | Preserve bytes. SCV may report diagnostics but must not replace a successful editor save with an older revision. |
| Private checkpoint | Yes | Durable exact snapshot with parse/schema status; do not require solver success. |
| Shared draft | Yes under confidentiality policy | Acknowledge durability, not correctness or acceptance. |
| Explicit verified commit | Depends on selected profile | Wait for required checks or reject promotion while retaining the private checkpoint. |
| Automatic build dispatch | Profile-specific | Skip/queue invalid or incomplete transactions; never compile a changing half-saved project as if it were a frozen candidate. |
| Protected source integration | Required source checks must pass | Exact parser/compiler/test and review evidence. |
| DB settlement | Required DB checks must pass | Schema, row, constraint, identity, causal, and authority evidence; source compilation only when the change actually requires it. |
| Release | Complete release profile | No substitution of `not_run` or `unavailable` for pass. |

For a strict editor workflow, offer **transactional accept-to-workspace**: edits remain in a private scratch overlay, and a valid transaction may replace the accepted working view. It is not a system-wide ban on saving invalid files. Always provide explicit recovery/export of rejected scratch content.

### 4.2 Source state and database state are separate

Do not impose a single sequence such as `parsed -> compiled -> tested` on all objects.

A source candidate can carry `syntax_status`, `compiler_status`, and `test_status`. A DB candidate carries `schema_status`, `constraint_status`, `reference_closure_status`, and `settlement_status`. Both have source-byte durability, provenance, authorization, and publication state. Status is derived from immutable receipts, not mutating a content-addressed commit to say it passed.

Tree-sitter success only establishes a grammar-specific parse result. Simple compiler parsing/type resolution remains authoritative for Simple semantics. DB schema validation is provided by the SDN database model, not by the absence of Tree-sitter ERROR nodes.

### 4.3 Avoid build and commit feedback loops

Each event carries an origin and transaction: `user`, `ide`, `agent`, `build_output`, `projection`, `scv_metadata`, or `import`. Build outputs and SCV-generated indexes must not trigger recursive source builds or metadata commits.

A build request identifies a frozen candidate and inventory generation. Save bursts are coalesced, obsolete pending builds may be cancelled, and completed results remain attached to the candidate actually built. A multi-file refactor closes at `transaction_end`, not after its first file write. Background parsing may finish later without altering the original checkpoint.

No automatic verified commit should be created merely because a parser became idle. Explicit policy decides which completed transactions are eligible, and source/evidence/policy changes invalidate prior eligibility.

---

## 5. SDN-only configuration and policy contracts

### 5.1 Native syntax and parser selection

SDN is a language, not YAML with a renamed extension. Use the actual Simple forms: indented mappings, quoted/bare values, inline arrays with `=`, and named tables such as `routes |id, domain, path, profile|`. The examples below follow the documented SDN forms, but their **SCV keys are proposed schemas** and have not been executed with the native parser in this document. [S01]

Implement configuration loading as:

```text
bounded full SDN parse
    -> duplicate-key/table-shape/limit checks
    -> versioned configuration-schema validation
    -> authority-policy intersection
    -> provider/profile resolution
    -> immutable effective configuration + digest
```

Do not use the documented flat-only `parse_config` function for these nested/table-bearing files. Reuse the strict SDN infrastructure where its complete parser contract is verified. Syntax limits do not replace semantic validation. [S01] [S02]

### 5.2 Configuration ownership and precedence

| File / location | Responsibility |
|---|---|
| `config/scv.sdn` | Repository topology, resource preferences, and references to named profiles/domain routes. |
| `config/scv-routes.sdn` | Versioned path/role-to-profile routing with explicit overlap and protected-role transitions. |
| `config/scv-policy.sdn` | Versioned shared authority policy; changes evaluated under the old accepted policy. |
| `config/scv-providers.lock.sdn` | Exact approved parser/solver/hash/codec artifacts and ABI/specification versions. |
| `config/scv-db/*.schema.sdn` | Database schemas, ColumnUid bindings, constraints, field-specific merge policies. |
| `plugins/<provider>/plugin.sdn` | Provider capabilities and required host ABI; installation does not automatically grant authority. |
| `.scv/local.sdn` | Local permitted preferences, offline pins, bounded caches; not a public policy source. |
| Host-managed SDN policy | Root-of-trust, executable-provider allowance, credential references, global resource ceilings. |

Ordinary preferences may use command-line > local > repository > built-in defaults. **Security/authority constraints are intersected, not overwritten by this precedence.** A CLI flag cannot enable network access for a solver or downgrade a protected hash policy. Credentials are references to a secret provider, never plaintext committed SDN values.

Unknown mandatory fields, duplicate keys, conflicting routes, invalid units, unresolved required provider pins, and unsupported required versions fail before promotion. Optional foreign metadata is isolated in an explicitly versioned extension namespace; silent typo acceptance is forbidden.

### 5.3 Repository configuration example

All numeric values here are initial evaluation settings, not measured optima. Time units appear in field names; byte values are integers.

```sdn
schema_version: 1
scv:
    topology:
        client_mode: "hybrid"
        shared_authority: "git_upstream"
        gateway_profile: "team_gateway"
        coordinator: "sj"
        allow_local_offline_revisions: true
    hashes:
        lookup_default: "xxh3_128"
        lookup_allowed = ["xxh3_128", "gxhash_128", "blake3_256"]
        durable_default: "blake3_256"
        secure_allowed = ["blake3_256", "sha256"]
        legacy_read = ["sha256"]
        compute_policy: "required_then_lazy"
        provider: "auto"
        isa: "auto"
        verify_fast_matches: true
        allow_secure_downgrade: false
    storage:
        source_layout: "syntax_nodes"
        source_boundaries: "complete_nodes_blocks_siblings"
        database_layout: "schema_row_value_records"
        target_record_bytes: 16384
        soft_max_record_bytes: 65536
        oversized_record: "stream_intact"
        codec_profile: "balanced"
        structural_delta_depth: 0
        retain_raw_copy: true
    capture:
        ordinary_save: "preserve"
        private_checkpoint: "allow_invalid"
        build_trigger: "validated_transaction"
        edit_debounce_ms: 150
        maximum_batch_delay_ms: 1000
        explicit_checkpoint_ack: "durable"
        fine_grained_edits: "coalesce"
        record_private_transcripts: false
    solvers:
        providers_lock: "config/scv-providers.lock.sdn"
        routes_file: "config/scv-routes.sdn"
        default_on_unknown_domain: "opaque_conflict"
        missing_required_provider: "block_promotion"
        ambiguous_route: "error"
        deterministic_default: true
        llm_proposals: false
        isolated_worker_memory_bytes: 268435456
        background_analysis: true
    database:
        identity_scheme: "actor_incarnation_counter"
        settled_aliases: "gateway_epoch_sequence"
        conflict_default: "explicit"
        schema_changes: "typed_operations"
        scalar_timestamp_winner: false
        lazy_constant_defaults: true
        causal_retention: "frontier_or_explicit_retirement"
        settlement_ack: "accepted_ref_verified"
    retention:
        private_checkpoint_policy: "reachable_then_reviewed_expiry"
        keep_unpublished_roots: true
        unresolved_conflicts: "pin_inputs"
        eviction_target: "rebuildable_caches_only"
        raw_reclamation: "disabled_until_restore_gate"
    execution:
        scheduler: "shared_build_runner"
        budget_required: true
        nested_thread_pools: false
        mandatory_grammar_download: false
```

`maximum_batch_delay_ms` bounds processing delay, not a promise that an editor save is already an acknowledged SCV checkpoint. Explicit checkpoint acknowledgements wait for their durability contract. A background capture queue must expose its unacknowledged window.

### 5.4 Routes example

The checked-in routing policy, not file extension alone, establishes content roles.

```sdn
schema_version: 1
routes |id, domain, path, profile|
    "scv_policy", "configuration_policy", "config/scv-policy.sdn", "protected_policy"
    "scv_configuration", "configuration", "config/scv.sdn", "sdn_config"
    "provider_locks", "configuration_policy", "config/scv-providers.lock.sdn", "provider_lock"
    "db_schemas", "database_schema", "config/scv-db/*.schema.sdn", "sdn_schema"
    "db_records", "database_data", "data/**/*.sdn", "sdn_rows"
    "simple_source", "source", "src/**/*.spl", "simple_source"
    "rust_source", "source", "src/**/*.rs", "treesitter_source"
    "documentation", "document", "doc/**/*.md", "markdown_document"
    "opaque_assets", "opaque", "assets/**", "opaque_conflict"
```

Require an explicit policy rule for overlapping matches. An implementation may support ranked specificity, but equal-ranked incompatible roles are errors, not “first plugin wins.” Renaming a protected file does not silently remove its protected role; verify role transitions against old and new paths and accepted metadata.

### 5.5 Solver profile and plugin manifest examples

Profiles select behavior; manifests describe capabilities. Neither is an executable script.

```sdn
schema_version: 1
profile:
    id: "sdn_rows"
    domain: "database_data"
    model_provider: "scv.model.sdn_database"
    solver_chain = ["scv.solve.db_identity", "scv.solve.db_fields"]
    validators = ["scv.validate.db_schema", "scv.validate.db_constraints", "scv.validate.db_references"]
    unresolved: "persist_conflict"
    line_merge_fallback: false
    ordered_list_default: "conflict"
    scalar_default: "three_way_conflict"
    output_format: "sdn"
```

```sdn
manifest_version: 1
plugin:
    id: "scv.solve.db_fields"
    role: "solver"
    abi: "scv_solver_v1"
    domains = ["database_data"]
    request_schema: "scv.solve_request.v1"
    result_schema: "scv.solve_result.v1"
    deterministic: true
    side_effects: "none"
    network: "deny"
    filesystem: "host_supplied_objects_only"
    clock: "deny"
    randomness: "deny"
    may_publish: false
    may_allocate_settled_ids: false
    may_change_policy: false
    implementation: "builtin_simple"
    max_output_ratio: 8
```

The sample output ratio is a resource ceiling, not an acceptance rule: combine a defined input-size basis with an absolute output limit, including empty-input cases. Exceeding a budget returns `resource_limited`, never a truncated success.

The real lockfile must bind this ID to an exact reviewed implementation artifact, specification/ABI version, compatible runtime, digest algorithm and digest bytes. A built-in implementation still needs a build identity. Symbolic provider IDs in examples are not valid substitute artifact pins. No fabricated digest is presented as installable configuration.

---

## 6. Parser, domain model, solver, validator, and publisher plugins

### 6.1 Five responsibilities, not one merge plugin

| Interface | Input | Output | Must not do |
|---|---|---|---|
| `ParserProvider` | Immutable bytes, grammar lock, edits | CST, errors, byte ranges, complete-byte coverage hints | Decide row identity, interpret DB constraints, authorize edits. |
| `DomainModelProvider` | Parsed/raw input plus schema/profile | Source entities, configuration keys, or DB tables/columns/rows | Infer privileged merge policies from arbitrary comments. |
| `SolverProvider` | Base/left/right models, verified operations, policy, budget | Candidate plan, conflicts, missing prerequisites, explanation anchors | Write live files, run arbitrary commands, allocate official aliases, publish refs. |
| `ValidatorProvider` | Frozen proposed output and exact required checks | Typed validation receipts with exact subjects | Accept a solver's self-reported success as independent evidence. |
| `Publisher` | Candidate, receipts, expected authority state, authorization | Durable acceptance or explicit refusal/retry | Reinterpret unresolved semantic conflicts as transport success. |

A native plugin may implement several interfaces, but the host still calls them through separate capability boundaries. Pure built-ins avoid unnecessary process boundaries. Untrusted/native third-party implementations run in isolated workers; approved WASM is another option after its actual sandbox contract is tested.

A signature identifies an artifact or publisher; it is not proof that the implementation is correct. Retain differential tests and independent host invariants.

### 6.2 Minimal typed request

The following is an interface sketch, not a second configuration language.

```text
SolveRequestV1
    request_id, repository, namespace, domain
    base_revision_ids[], left_revision, right_revision
    base_model_ids[], left_model_id, right_model_id
    expected_source_or_db_root
    schema_revision, policy_revision, routing_revision
    parser_lock_digest, solver_lock_digest
    compiler_configuration_digest (when relevant)
    verified_operation_bundles[], identity_map_revision
    authorization_scope, readable_object_capabilities
    logical_work_budget, memory_budget, cancellation_token

SolveResultV1
    request_id, status
    candidate_plan_id?, candidate_root?
    typed_operations[], exact_byte_effects[]
    conflicts[], required_reads[], required_checks[]
    evidence_refs[], provenance, resource_counters
    completeness, deterministic_result_key
```

Statuses are `unchanged`, `proposed`, `conflicted`, `needs_inputs`, `unsupported`, `resource_limited`, `cancelled`, or `failed`. There is no solver status named `published` or unqualified `safe`.

The host supplies immutable objects by handles and bounded reads, not ambient filesystem paths. Serialized interfaces use versioned binary records for throughput and SDN inspection/export. Never share raw compiler/parser pointers across processes.

### 6.3 Provider lifecycle

Implement discover -> install explicitly -> verify artifact/ABI -> register capabilities -> resolve profile -> execute -> validate -> retain result/provenance -> upgrade through a new generation.

No automatic download on normal capture. An offline missing plugin must not block byte preservation. Missing required solvers/validators block verified promotion and return a typed capability error.

Provider selection is resolved once per transaction/profile. Avoid dynamic name lookup for every token, row, or cell. Batch neighboring work under one immutable schema/profile while retaining per-record identities and errors.

### 6.4 Determinism and bounded execution

A result-cache key includes domain, all relevant base/side inputs, schema, policy, routing, identity-map revision, parser/query/provider artifacts, effective configuration, and authorization scope.

Use deterministic candidate ordering and logical limits such as compared-pair count. Wall-clock timeout can cancel work, but must not cause “the first candidate that happened to finish” to become the authoritative merge. A retry may obtain a fuller result; the prior partial outcome is explicit.

LLM-assisted solvers are optional proposal producers. Record model/tool/context identities; do not call them deterministic merely by setting a seed. Their results pass the same validators and review requirements. A model cannot resolve an identity mapping by inventing a missing ID.

---

## 7. Deterministic routing and solver composition

### 7.1 Route by semantic role, then representation

A `.sdn` suffix selects an SDN parser, not a universal solver. The same syntax can represent configuration, a database schema, data rows, plugin metadata, or test evidence. Bind the domain using an accepted route/schema manifest. Payload self-declarations are checked against that binding, not trusted by themselves.

Routing sequence:

1. Resolve the accepted authority/policy/routing generation.
2. Determine the object domain and allowed transition from its old role.
3. Load the required parser and domain model.
4. Resolve the pinned solver chain and required validators.
5. Preserve all source inputs and run the plan without live writes.
6. Validate the entire candidate, including cross-file/table dependencies.
7. Publish through the appropriate authority only after evidence is complete.

A routing or solver-policy edit in the candidate is solved using the old accepted routing policy. It becomes active only for subsequent requests after authorized acceptance. This prevents a patch from redefining its own validator.

### 7.2 Initial solver catalog

| Provider family | Main responsibility | Safe default when incomplete |
|---|---|---|
| `source.identity` | File/entity alignment from verified rename/refactor evidence | Preserve ambiguity. |
| `source.syntax` | Independent node/block three-way merging | Explicit structural conflict or limited raw fallback. |
| `source.semantic` | Compiler-backed transformations and dependency checks | Unavailable/needs validation. |
| `db.schema` | Table/column identity and migration reconciliation | Schema conflict; no line-union substitute. |
| `db.fields` | Three-way scalar/cell edits and declared set/list behavior | Scalar/list conflict. |
| `db.constraints` | Uniqueness, references, nullability, type and cross-row checks | Block settlement. |
| `config.sdn` | Schema-typed settings, named records, declared set/list policies | Conflicting setting or policy review. |
| `document.markdown` | Sections/anchors, with conservative order handling | Text/structural conflict. |
| `opaque` | Same-content/unchanged-side rules for binary or unknown content | Keep both sides; request human resolution. |

Constraint checking is a validator role even when packaged with a DB plugin family.

### 7.3 Composition rules

Schema resolution precedes row interpretation. Identity resolution precedes source move alignment. Provider-lock or routing changes require separate policy validation. Build/generated-content validation happens after a complete candidate is frozen.

Do not let two plugins mutate overlapping output ranges independently. They return typed plans; the host combines disjoint plans, detects overlap, and validates the combined result. “Both plugins individually passed” is insufficient when their combination changes a shared invariant.

For a DB cell declared to contain source code or Markdown, a subsolver may operate on that cell's exact bytes with an explicit subprofile. It cannot access other tables or files unless the parent request grants them. The parent DB validator still checks the final row and transaction.

Fallback is domain-specific. Ordinary source may use conservative text merging. A schema-bound DB file may be preserved as an unresolved raw draft when its DB solver is absent, but must not be admitted through text merge just because it has no conflict markers.

---

## 8. Source-code solver family

### 8.1 Evidence-backed integration ladder

1. Exact same-content/unchanged-side checks, including file kinds and modes.
2. Revision-specific FileUid and EntityUid alignment using validated OS/editor/agent operations.
3. Three-way merge of disjoint verified node edits.
4. Language-profile-approved structural rules, with order sensitivity preserved.
5. Compiler-backed symbol/refactor rules when semantic inputs are available.
6. Reusable prior resolution proposal under exact matching preconditions.
7. Optional bounded LLM proposal.
8. Explicit conflict with preserved base/sides/candidates.

Tree-sitter supports edit-and-reparse with old-tree reuse; it does not itself establish durable entity identity or semantic equivalence. Mergiraf provides a useful reference for structured merging and language-specific commutative contexts. [R02] [R03]

### 8.2 Typed operations

Support file move/copy/delete, directory move, node replace/move, symbol rename, signature change, and exact text edit. Bind every operation to base revision, expected identity/content, operation producer, sequence/dependencies, and transaction.

`CopyFile` allocates a new logical identity with `copied_from`; `MoveFile` retains identity only when the operation and its effects are verified. A copy followed by delete is not automatically a move. Directory moves expand through a frozen membership map rather than a live directory walk at merge time.

An inode/file handle is useful local evidence, not a globally stable identity. Account for inode reuse, file replacement, hard links, cross-volume moves, symlinks, and case-only renames. Hard-link relationships are explicit metadata; two paths sharing content are not necessarily one source entity.

### 8.3 Revision-aware identity, not one current-path table

Keep immutable identity maps per revision, built with persistent substructure and checkpoints. Merge uses all relevant parent lineages, not only whichever path currently exists in a mutable workspace table. Do not replay an unbounded first-parent history on every merge.

A stable entity ID locates the logical target but never waives content preconditions. Rename-versus-body-edit can be compatible; rename-versus-incompatible-signature change may not be. Ambiguous identical declarations remain separate identities.

### 8.4 Source validation

Validate byte reconstruction, parser result for the selected language, entity uniqueness/binding, required compiler configuration, impacted dependencies, and required tests. Parsing and compilation can be unavailable locally; such a candidate remains a draft or requires remote validation.

Do not use the current text merge validator's blanket empty-output/NUL rule as the repository byte rule. Empty source files may be legal, binary objects are not text, and conflict-like strings can legitimately occur inside literals. Detect unresolved conflicts from typed conflict state and language-aware checks. [S09]

Order-sensitive imports, side-effecting declarations, macros, static conditions, generated code, and configuration-specific references must remain conservative. An AST-shape match is not behavioral equivalence.

---

## 9. Textual database schema solver

### 9.1 Columns are entities, not positions or strings

Extend the existing UID system to `table`, `column`, `constraint`, and `migration` kinds. A column has:

```text
ColumnIdentity = namespace + kind + actor_incarnation + counter
ColumnDefinitionRevision = secure canonical digest of definition
ColumnDefinition = table_uid, column_uid, name, logical_type,
                   nullability, default_rule, constraints,
                   merge_policy, visibility, state
```

Column names and display order are attributes. A column rename changes the name, not ColumnUid. Dropping and recreating the same name produces a new ColumnUid; old data does not silently reappear. Iceberg's field-ID approach is useful prior art for this distinction, not a proposal to adopt its storage engine. [R04]

The inspected DB operations are primarily row/value operations with name-based fields. Add a new versioned schema-operation contract instead of pretending an `AddColumn` already exists in that enum. [S04]

### 9.2 Schema operations

Implement `CreateTable`, `AddColumn`, `RenameColumn`, `DropColumn`, `MoveColumnPresentation`, `AlterType`, `SetDefault`, `SetNullability`, `AddConstraint`, `DropConstraint`, and explicit migration bundles. Each binds the base schema, expected prior definition, table/column UIDs, policy, and operation dependencies.

Changing a field's merge policy is itself a schema/policy change. Historical operations retain the reducer version they were authored under; do not reinterpret an old observed-remove event as a remove-wins event merely because a configuration file changed.

### 9.3 Concurrent schema decision table

| Concurrent changes | Default result |
|---|---|
| Add different names with distinct UIDs | Merge if combined constraints and dependencies remain valid. |
| Replay identical `AddColumn` with same operation ID and payload | Idempotent acknowledgement; no new column or alias. |
| Same UID but different definitions | Collision/divergence error; preserve both proposals. |
| Same name, different UIDs, same apparent definition | Keep identity distinction; explicit equivalence policy/review required before coalescing. |
| Same name, incompatible types/defaults/policies | Schema conflict. |
| Rename column while another side updates its values | Rebind by ColumnUid; validate old-schema operation against new definition. |
| Rename the same column to two different names | Rename conflict, not timestamp winner. |
| Drop column while another side edits it | Tombstone/update conflict; retain data and proposed edits. |
| Drop then recreate same name | New identity; never alias to dropped data implicitly. |
| Add `NOT NULL` column with no applicable default | Require backfill/migration; do not accept only the schema header. |
| Add two individually valid constraints that conflict together | Reject combined candidate; validation is transaction-wide. |
| Reorder presentation columns on both sides | Preserve stable identities; merge order only under an explicit list-order policy. |

### 9.4 Old-schema writes and defaults

Every write references its schema revision. A migration adapter maps old ColumnUids/types into a new schema with explicit preconditions. No mapping means `schema_incompatible`, not guessed field alignment.

Represent at least **Absent**, **Null**, **Value**, and **Tombstoned** distinctly. Absence in an older row schema is not an explicit null. A lazy constant default may supply a view without rewriting every row. Bind the default to the introduction/migration rule and schema revision; changing the future-write default must not retroactively change historical row meaning.

Nonconstant defaults, cross-row expressions, randomness, or current-time defaults require explicit evaluated values or a pinned deterministic migration. Do not evaluate `now()` independently on each replica and call the result identical.

### 9.5 SDN schema example

This fixture uses readable UID labels for illustration; production references use the existing structured identity encoding. The strings below are not claimed to be accepted by today's identity parser.

```sdn
schema_version: 2
database_namespace: "demo_tasks"
table_uid: "table_fixture_tasks"
schema_revision: "schema_fixture_17"
columns |column_uid, name, logical_type, nullable, merge_rule|
    "column_fixture_id", "id", "entity_ref", false, "identity"
    "column_fixture_title", "title", "text", false, "scalar_conflict"
    "column_fixture_labels", "labels", "text_set", false, "observed_remove_set"
    "column_fixture_priority", "priority", "u64", true, "scalar_conflict"
constraints |constraint_uid, kind, column_uid, target|
    "constraint_fixture_pk", "primary_key", "column_fixture_id", "self"
```

Implement schema resolution through IDs; do not embed new unverified annotation syntax such as a proposed `@merge` grammar in the core parser merely to express a field policy. The named-table representation can carry policies directly and can later support reviewed sugar that lowers to the same model.

---

## 10. Textual database row and value solvers

### 10.1 Merge cells and records, not lines

Build on existing `DbPatch`, `MergePolicy`, and reducer implementations. A v2 cell address is `(TableUid, RowUid, ColumnUid)`. Expected values and row/schema revisions provide preconditions. Name-based v1 operations are resolved through their original schema before conversion. [S04] [S05]

For each ordinary scalar field, the basic three-way rule is:

```text
left == right       -> that value
left == base        -> right
right == base       -> left
otherwise           -> explicit concurrent-value conflict
```

These rules do not validate references, uniqueness, nullability, or business constraints; the combined candidate must still pass transaction-wide validators.

### 10.2 Field-specific policies

| Field kind | Solver behavior |
|---|---|
| Identity/reference | Resolve UID/alias under an authenticated mapping; never infer from a number alone. |
| Ordinary scalar | Three-way conflict rule; no default LWW. |
| Ordered list | Preserve order and element identity where supported; conflicting order edits remain explicit. |
| Observed-remove set | Preserve operation dots and observed removals; do not reduce to plain set union. |
| Add-wins/remove-wins set | Only the specifically declared, versioned algebra; no silent interchange. |
| Counter | Merge increments only when the schema declares counter operations; assigning a new total is not an increment. |
| Append-only observations | Union by immutable event ID; same ID/different payload is corruption or conflicting evidence. |
| Derived field | Recompute under the pinned derivation; reject direct writes unless explicitly permitted. |
| Authority-controlled field | Verify the authorized producer and scope; not “latest timestamp wins.” |
| Long text/embedded source | Optional scoped subsolver; parent row constraints still govern acceptance. |

Automerge illustrates that convergence and preserving concurrent values are distinct from having one semantically correct scalar answer. SCV should expose unresolved alternatives instead of hiding them behind a deterministic display winner. SQLite changeset conflict categories are a useful reference for separating data mismatch, missing row, duplicate key, and constraint failures. [R05] [R06]

### 10.3 Constraint closure and write skew

Two edits to different cells can still violate a shared invariant. Examples: both writers allocate the same natural key; two rows each remove the final required owner; a delete and a new foreign-key reference race; individually valid numeric changes violate a sum limit.

Validators must check a sufficient read set, relevant index roots, or the current transaction snapshot. At acceptance, recheck against the current authority generation or re-run after CAS failure. Per-cell independence alone does not provide serializable DB semantics.

Natural-key equality does not automatically prove entity equivalence. A schema may define a reviewed coalescing rule; otherwise retain two provisional identities and a duplicate-key conflict. This is especially important for people, tasks, bug reports, and configurations that merely share a label.

### 10.4 Human-editable SDN and authority

Use one declared authoritative model per DB, not two independently writable truths.

**Small text mode:** SDN schema and table files are the authoritative authored text. Capture exact bytes, parse against the declared base schema, derive a typed batch, and accept only after validation. Stable identity columns/header bindings prevent reordering from changing meaning.

**Scalable typed mode:** Immutable typed batches plus schema/checkpoint manifests are the authoritative semantic history, with SDN text representation and an optional versioned binary encoding of the same logical records. Binary pages/indexes accelerate access. Human-edited SDN projections are imported as proposals against the projection's exact base revision, never silently treated as a second database.

Do not require a new SQL server. A local directory/bundle and a gateway-backed or Git-backed settlement ref can implement both modes.

### 10.5 Avoid full-table rewrites

Adding a nullable/defaulted column can update schema metadata while older row batches retain their original schema stamp. Store rows/field maps by stable column identity and materialize defaults lazily. Shard at complete tables, row batches, or records—not arbitrary source-byte cuts.

A wide human-readable table with the new column printed on every row necessarily costs O(number of rendered rows) to regenerate. Do not claim the textual export is O(1). Avoid rendering it on every keystroke; update the typed store/index first, and render requested/exported views at controlled boundaries.

Malformed row widths, duplicate headers, lost identity columns, or unknown schema mappings block semantic import. Preserve the submitted bytes as a private draft; do not silently pad cells, realign columns by position, or drop unknown data.

---

## 11. Stable identities, clocks, compact aliases, and settlement

### 11.1 Reuse the actual identity system

The repository already defines:

```text
EntityUid = database_namespace + entity_kind + ActorIncarnation + counter
SettledAlias = database_namespace + authority_epoch + entity_kind + sequence
```

Use this for tables, columns, rows, constraints, and other stable DB entities. The original UID remains permanent; “temporary” means not yet assigned a compact alias, not disposable identity. [S03]

A displayed `#10235` must be resolved with its namespace, epoch, and kind. Never persist or interpret an unqualified bare integer as globally unique. Aliases and typed reference mappings survive export, restore, and schema changes.

### 11.2 Offline creation and time

Generate a sufficiently random actor incarnation and persist/lease counters before acknowledging allocations. Independent worktrees can share a safe allocator or use distinct incarnations. Cloning/restoring an actor state onto another live machine requires a new incarnation; do not reuse an old counter stream.

Track three independent concepts:

| Value | Purpose | Not a substitute for |
|---|---|---|
| `created_at` | Human display and diagnostics | Unique identity or conflict winner. |
| Causal dependency IDs / actor counters | Happens-before information and replay requirements | A universal wall-clock ordering. |
| Accepted settlement sequence | Compact canonical alias/order within a namespace | Offline creation chronology. |

An optional hybrid logical clock can help ordering diagnostics, but cannot on its own establish that two operations were concurrent or that one value should win. Preserve actual causal dependencies/frontiers.

### 11.3 Gateway settlement protocol

1. Client durably records a batch with stable operation IDs, original UIDs, base revision, schema/reducer/profile versions, dependencies, and canonical payload digest.
2. Gateway authenticates the request, checks replay identity, and fetches the complete required schema/reference closure.
3. Source/config/DB schema/data solvers run as appropriate; unresolved conflicts stay drafts.
4. Validators check the combined candidate and authority policy.
5. Allocate **candidate** aliases from the current accepted allocator state, preserving existing UID bindings.
6. Build one acceptance candidate containing schema/data changes, UID-to-alias bindings, allocator high-water marks, accepted-batch records, and receipt inputs.
7. Conditionally publish against the expected authority head.
8. On a race, reload accepted state, replan, and retry idempotently. Candidate numbers are not public promises.
9. Verify acceptance through authoritative read-back; only then return the final settlement receipt.
10. Client records the receipt and updates its alias index. Original UIDs and historical operations remain unchanged.

Existing `db_allocation.spl` already plans original-UID and settled-reference projections together. Extend and verify that path rather than adding a second independent allocator. [S07]

### 11.4 Linearization under each deployment

| Authority mode | Moment aliases become settled |
|---|---|
| Local-only sandbox | Local namespace's durable accepted transaction; aliases remain local namespace values. |
| Git/GitHub-authoritative settlement | Accepted protected settlement-ref update containing mappings/data, followed by verified read-back. Merely publishing a PR/topic branch is not settlement. |
| Native gateway authority | Durable native acceptance transaction/CAS for that namespace; Git mirroring is a later delivery state. |

A gateway must not both promise aliases before GitHub acceptance and claim GitHub is the sole settlement authority. Choose one contract.

No gapless-number guarantee is required. Never recycle accepted aliases. Epoch changes need explicit migration/fencing and retained mappings; they are not permission to reinterpret old integers. Counter or sequence exhaustion fails explicitly or creates a reviewed new epoch/incarnation.

### 11.5 Uncertain acknowledgements and cross-resource changes

If acceptance succeeds but the response is lost, retry by batch ID plus payload digest, inspect accepted history, and return the same mapping. Same ID/different payload is rejected. Never regenerate a new UID merely because a network request timed out.

A schema/data/alias transaction should use one acceptance root. Multiple unrelated Git refs or repositories are not automatically an atomic transaction. When source and DB changes must land together, either place them in one accepted commit/root or use an explicit prepared-bundle/activation-manifest protocol with dependency checks and recoverable intermediate states. Do not call two successful pushes atomic.

### 11.6 Causal compaction and long-offline clients

Keep aliases and identity tombstones necessary to interpret retained history. Causal event dots and delete tombstones may be compacted only when a proven stability frontier or explicit replica-retirement/checkpoint protocol makes replay safe.

Time-to-live alone is insufficient: an old offline replica could otherwise resurrect deleted values. A client returning from before the retained causal frontier must rebase/reseed through a full checkpoint and receive explicit stale-base handling, not silently apply its old deltas.

---

## 12. SDN configuration solver

Configuration is neither source text nor a generic database table. It uses its own schema-governed merge profile.

Independent mapping keys may combine. Incompatible edits to the same scalar conflict. Lists remain ordered unless their schema declares set semantics. Named configuration tables merge by explicit stable key, not line number. Duplicate keys/route IDs/provider names are errors even when a permissive parser would accept the last occurrence.

Security-sensitive settings—provider allowlists, secure-hash minimums, executable permissions, protected refs, credentials, settlement epochs, and solver routing—require old-policy authorization. A candidate cannot replace `scalar_conflict` with `last_writer_wins` to approve itself.

Do not interpret `${...}` or similar string content as an executable interpolation unless the schema explicitly supports a bounded reference mechanism. Secret references are resolved by the host at runtime and excluded from normal generated views and logs.

Formatting/comments remain attached to the exact submitted text. Semantic canonicalization can produce an effective configuration digest without replacing the raw content digest. Preserve unresolved choices in typed conflict objects, not duplicate-key SDN that looks accepted to downstream tools.

---

## 13. Conflict objects, resolution receipts, and reuse

### 13.1 Durable conflict representation

A conflict contains its domain, type, exact base/side revisions, affected entity/column/path, submitted operations, schema/policy/provider identities, competing values or node references, diagnostics, and any candidate attempts. Keep content references instead of duplicating entire files in each conflict record.

Examples include `source.identity_ambiguous`, `source.signature_incompatible`, `db.schema_name_collision`, `db.type_migration_required`, `db.scalar_concurrent`, `db.reference_missing`, `config.policy_change`, `provider.unavailable`, and `resource.incomplete`.

Unresolved conflicts remain valid private/draft repository states. Jujutsu's first-class conflict model is useful precedent for preserving logical conflicts rather than treating text markers as the stored truth. This does not establish that jj inherently creates more conflicts; compare actual workloads. [R07]

### 13.2 Resolution is another immutable operation

A resolution binds the conflict ID, exact chosen/revised result, actor/authority, policy, validation receipts, and whether it supersedes an earlier proposal. Human and model resolutions use the same preconditions. A human may approve a policy exception, but that exception is explicit evidence—not a fabricated passing test.

### 13.3 Safe resolution reuse

Adopt a domain-aware analogue of Git `rerere`: retain a prior resolution proposal and reuse it only when the conflict's inputs, identity mappings, schema/profile, policy, and meaningful surrounding context match. Git documents reuse of recorded conflict resolutions; SCV adds richer domain keys and revalidation. [R08]

Exact reuse may avoid recomputing a deterministic solver. It does not automatically reuse changed compiler/test results or expired authorization. Approximate similarity produces a suggestion, not automatic acceptance. Pin unresolved input closures, but make abandoned candidate attempts eligible for reviewed retention policies.

---

## 14. OS, shell, IDE, and LLM operation capture

### 14.1 One event schema, several adapters

Capture `begin`, exact operation, observed effect, `end`, and verification outcome. Include repository/workspace, transaction, actor/run, base generation, entity hints, old/new paths, old/new content IDs, sequence/causal dependencies, and origin.

| Source | Integration target | Limitation / required verification |
|---|---|---|
| Simple OS filesystem service | Emit compact records after successful operations, with transaction/generation context | Intent and success must be distinguished; filesystem durability still has a stated boundary. |
| Hosted `cp`/`mv`/rename wrappers | SCV-aware commands or Simple shell adapters | Programs can bypass wrappers; verify actual effects and retain watcher fallback. |
| IDE/LSP/Neovim | Buffer edit transactions, file operations, refactor metadata | Byte coordinates, version, and old content must match; editor identity hints are not authority. |
| LLM tool wrapper / Caret / Spipe | Capture structured file-tool requests, execution status, and output digests | A command string or claimed result is not evidence of execution. |
| Native filesystem watcher | Dirty hints, pairing where available, overflow/restart detection | Not a complete intent log; lost/coalesced events require reconciliation. |
| Full scan | Recovery and cursor reconciliation | More expensive, but required when event completeness cannot be established. |

Do not require privileged global syscall interception. Optional tracing can improve coverage but must be measured and must not become a correctness prerequisite.

### 14.2 Integration work

Replace the documented spool-only IPC limitation with a tested native transport: Unix-domain sockets where appropriate, Windows named pipes or another authenticated local channel, and a Simple OS service endpoint. Retain a bounded fallback where needed. Reuse the same message codec and transaction model rather than creating a different protocol for each editor. [S08]

Record preconditions before mutation where a tool supports it and effects after completion. An operation denied by the OS is not committed intent. Atomic-save temporary rename sequences must be normalized without confusing them with a deliberate user-level file move.

### 14.3 Snapshot correctness and overhead

A stable read of each individual file does not automatically make a multi-file project snapshot atomic. Use an inventory generation, transaction boundaries, or retry/drift checks. Watcher sequences are hints; same size/coarse mtime cannot erase an explicit dirty event.

On the synchronous path, record minimal operation metadata and preserve the save. Coalesce editor edits before expensive parsing/indexing. Do not calculate all hashes, serialize full buffers, create commits, or run builds for every keystroke.

Verify operation evidence against before/after snapshots. Missing events reduce optimization/identity confidence and trigger inference/reconciliation; they must not lose source history.

---

## 15. Configurable multi-hash infrastructure

### 15.1 Purpose, algorithm, provider, and ISA are different settings

| Purpose | Default | Allowed policy |
|---|---|---|
| Trusted lookup / candidate fingerprint | XXH3-128 | GXHash-128 or another approved fast/secure algorithm may be selected. |
| New native durable content/object identity | BLAKE3-256 | Another approved cryptographic algorithm such as SHA-256 with a distinct tagged identity. |
| Untrusted import/shared-cache verification | Expected approved secure algorithm | Never negotiate to XXH3/GXHash. |
| Legacy SCV objects and DB v1 records | Original SHA-256 semantics | Read/verify unchanged; explicit versioned migration. |
| Git objects | Git backend's object format | Separate Git OID mapping; not raw BLAKE3. |
| Authentication/signature | Separate approved primitive | Neither plain BLAKE3 nor an AES-based fast hash supplies authorization. |

Use `Cyan4973/xxHash` and `BLAKE3-team/BLAKE3` as principal conformance/reference implementations. GXHash is an optional trusted-boundary provider. Upstream describes it as noncryptographic and stable within a major algorithm version on supported platforms; pin its specification/version and hardware requirements. [R09] [R10] [R11]

### 15.2 Concurrent algorithms without unnecessary work

Resolve the required hash set per consumer. A single immutable byte stream can feed multiple supported streaming states, but CPU cost still grows with each algorithm. Calculate secondary digests lazily or during explicit migration; do not run every configured provider for every tiny node.

Provider capabilities must state streaming support and update semantics. Do not assume a generic language `Hasher.write` API yields a file digest independent of how input is split. If a GXHash implementation is only suitable for bounded one-shot input, use it for those nodes; do not buffer an unbounded file or invent a new chunk-combination algorithm under the GXHash name.

Auto-selection may choose a different fast algorithm only with the correct algorithm tag and consumer capability. Falling back from GXHash to XXH3 must not return XXH3 bytes labeled GXHash. A missing secure provider blocks secure admission or uses an explicitly approved alternative with its true identity.

### 15.3 Identity, encoding, and migration

Digest references include algorithm specification ID, mode/seed profile where applicable, output length, and canonical bytes. Provider build/ISA belongs in execution provenance unless it changes output semantics. GXHash major-version changes require distinct algorithm-specification IDs.

Domain-separate structured records with typed, length-framed canonical bytes. Use stable canonical integer encoding and explicit map/list/set semantics. Never hash native pointer layouts or ambiguous delimiter concatenations as authoritative identity. Raw source IDs hash raw bytes; semantic config/DB digests hash their canonical typed model.

When migrating, validate old bytes and references, compute new identities, and record verified aliases. Securing only an outer root while leaving unchecked weak descendants is insufficient. Existing DB v1 SHA-256 payload rules remain readable; introduce v2 envelopes rather than changing their meaning in place. [S04]

### 15.4 Provider qualification and dispatch

Test official vectors, arbitrary streaming splits where supported, empty inputs, lengths around block/chunk boundaries, large inputs, unaligned buffers, error propagation, and forced scalar/SIMD results. Hardware dispatch must be safe for the actual host and operating-system state; user flags cannot enable absent instructions.

The current shared Simple BLAKE3 source describes arbitrary-length support. This replaces the old plan's specific short-input defect, but does not eliminate the need for complete execution-based qualification. Reuse/consolidate shared implementations instead of adding SCV-private copies. [S11]

Use the shared build-runner resource budget. Many tiny nodes should be batched, not each assigned a nested thread pool. Optional BLAKE3 parallel updates use explicit provider support; upstream C documentation distinguishes normal update from optional parallel integration. [R10]

---

## 16. Structural storage, compression, and exact reconstruction

### 16.1 Source and database boundaries are related but not identical

| Domain | Logical reusable units |
|---|---|
| Parsed source | Complete syntax nodes, blocks, declarations, statements, and complete sibling runs. |
| SDN configuration | Mapping entries, named records, sections, ordered list elements, exact trivia/gaps. |
| Textual DB | Schema definitions, complete rows, typed fields/values, record batches, exact text occurrence metadata. |
| Unknown/binary/error region | Explicit opaque complete object/span; stream if large. |

The DB model defines row/column identity and merge semantics. Tree-sitter can preserve an SDN text representation, but it cannot decide that two similarly spelled columns are the same field.

### 16.2 Lossless DAG and representation separation

Retain the prior plan's distinction:

```text
RawContentId       = secure digest of exact file bytes
ByteNodeId         = secure digest of an ordered reconstruction record
SemanticModelId    = secure digest of a typed domain model + its schema/profile
RepresentationId   = secure digest of codec/layout metadata + encoded bytes
EntityUid          = logical identity, not any of the above hashes
```

A reusable byte node contains ordered inline bytes, complete child references, and/or payload references with exact lengths. Preserve gaps, punctuation, comments, invalid regions, and repeated occurrences. Store absolute path/offset in occurrence metadata, not every shared node.

For source injections, one host partition owns the bytes; embedded-language trees are overlays unless nonoverlapping ownership is explicitly delegated. Never duplicate bytes by concatenating overlapping parse trees.

### 16.3 No arbitrary source chunking

Choose boundaries through a versioned structural profile. Inline tiny pieces, descend through complete child nodes for oversized blocks, and stream an indivisible giant literal intact. Soft size targets guide selection but do not authorize a cut at byte N.

Unparsed or unsupported input is retained as explicitly opaque data or a declared fallback structure. Legacy CDC objects keep their readers; no new parsed-source writer silently falls back to CDC.

Physical codec blocks, pack pages, transport frames, and BLAKE3's internal algorithm chunks are not logical source units. Batching many complete records is allowed and important for efficiency.

### 16.4 Compression and restoration

Ship uncompressed records plus optional LZ4/Zstandard-style codec providers through the existing compression infrastructure. Hash-cons unchanged complete nodes with collision-safe equality. Prefer normal compression and subtree reuse before optional bounded structural deltas.

The initial structural delta depth is zero. Any later delta profile must declare/retain bases, verify reconstructed results, and bound decode depth, memory, and output. Dictionaries are reconstruction dependencies and GC roots.

Initially keep raw representations alongside structural representations for shadow comparison. Reclaim redundant raw copies only after independent parser-free restore, crash, GC, and backup gates. A reconstruction recipe becomes durable source data when it is the only remaining way to recover the bytes.

A whole-file BLAKE3 digest is not obtained by concatenating function hashes. New node records can be hashed incrementally while full-file raw hashing may still cost O(file size). Deferred raw digests are an explicitly gated private-checkpoint optimization, never a substitute secure identity for APIs requiring the raw digest.

---

## 17. Bounded growth, durability, scheduling, and cache reuse

### 17.1 Retention classes

| Class | Examples | Retention rule |
|---|---|---|
| Authoritative source/data | Accepted revisions, private unexported work, DB schemas/batches | Keep promised roots and complete reconstruction/reference closures. |
| Required interpretation metadata | UID/alias dictionary, schema migrations, reducer versions, tombstones/frontiers | Keep as long as retained/offline operations can require them. |
| Conflict/recovery roots | Unresolved conflicts, interrupted transactions, pending exports | Pin inputs until resolved or explicitly abandoned under policy. |
| Evidence | Required tests/reviews/settlement receipts | Retain according to audit policy; deletion cannot retain a stronger claim. |
| Rebuildable acceleration | CST indexes, field indexes, postings, cached plans, embeddings | Evict under budget; report pending/unavailable during rebuild. |
| Ephemeral fine edits | Keystroke-level events not promised as durable history | Coalesce/drop only after a checkpoint or transaction preserves required effects. |
| Sensitive optional sidecars | Agent prompts, terminal transcripts | Opt-in, protected, independently limited; never publish by default. |

### 17.2 Safe coalescing

Within an unobserved editor transaction, repeated replacement of the same region may be compacted into base-to-final edits. Preserve the final bytes and transaction attribution. Do not coalesce across an acknowledged checkpoint, external observation, refactor boundary, or causal dependency.

For DB scalar assignments, collapse only when intermediate values were not observed and the schema permits it. Do not collapse away increments, append-only observations, set dots, delete/recreate identity, or migrations with meaningful intermediate states.

Deduplicate source bytes and event metadata independently. A shared content hash is not permission to merge separate rows, source entities, or actor events.

### 17.3 Avoid redundant index work

Share one immutable capture and derived-data scheduler across SCV, IDE, compiler/build runner, and test runner. Cache by exact relevant input/schema/provider/policy versions. Coalesce concurrent derivations by key. Prioritize interactive requests and publication-critical validation; defer history-wide matching, embeddings, and recompression.

Resolve providers once per transaction. Reuse parser sessions, row/schema indexes, verified hashes, and previously computed source models. Use dense/compact handles locally with full collision-checked identity mappings; 16/32-bit handles are process/store-local references, not globally authoritative hashes.

### 17.4 Memory and I/O budgets

Every parser/solver job receives a shared CPU, memory, and I/O budget. Support fiber and process execution through common contracts; isolate untrusted providers without duplicating entire input trees. Share immutable mapped/buffered records where the platform safely permits it.

Avoid one RPC, file, allocation, or fsync per tiny syntax node or DB cell. Batch complete records and journal frames. Group commit may share an fsync across checkpoints, but an explicit durable acknowledgement occurs only after the promised state is durable.

On queue overflow or memory pressure, preserve source, record incomplete fine-grained capture, and schedule reconciliation. Never silently drop an acknowledged operation. On disk exhaustion, return a durability failure and retain the editor's bytes; do not report a checkpoint that does not exist.

### 17.5 Quantitative accounting without invented speedups

Track total coexistence storage:

```text
native payloads + reconstruction records + indexes + dictionaries
+ aliases + causal metadata + conflicts + evidence + pending publications
+ retained raw copies + Git compatibility storage + replicas
```

Measure steady-state growth and replay time, not just compressed payload size. Checkpointing must reduce replay bounds without breaking causal semantics. Declare an offline retention/frontier contract; unlimited offline delta replay and finite causal metadata are not automatically compatible.

Set project-specific budgets before promoting optimizations. Numeric defaults in example SDN are hypotheses to benchmark, not guaranteed limits on every parser's inherent work.

---

## 18. Native SCV gateway and Git/GitHub publication

### 18.1 Responsibilities

The gateway provides authenticated native object transfer, draft storage, checkout-free queries, pinned solver execution, validation orchestration, DB settlement coordination, and a durable Git publication outbox. Read caches are not additional publishers.

Fully SCV-native hosts upload/fetch native objects and metadata. A gateway-side bare Git store and typed adapter reconstruct selected file bytes and map native revisions to Git blobs/trees/commits. Git's import and conditional-ref facilities are interoperability references, not substitutes for SCV policy. [R12] [R13]

### 18.2 Distinct acknowledgements

Use explicit stages: `local_durable`, `gateway_durable`, `export_prepared`, `upstream_branch_published`, `review_pending`, `upstream_accepted`, and `accepted_result_imported`. DB alias acknowledgement follows the configured settlement authority, not whichever stage is convenient.

The native protocol advertises object formats, secure hash algorithms, codec support, domain/solver capabilities, and limits. Missing objects are requested by immutable ID in bounded batches. Input claims remain untrusted until verified. Authorization applies even on a cache hit.

### 18.3 Export semantics

Support faithful public-history export and selected publication export as separate policies. Intermediate private snapshots, conflicts, secret-bearing transcripts, and internal schema drafts need not become Git commits. Parent relationships must not accidentally publish private history.

Store mappings qualified by export policy, parent mapping, and backend object format. Recompression does not change source bytes; Git conversion still requires the complete logical bytes for each newly represented file version. Stream reconstruction where possible; no full working-tree checkout is required merely to produce blobs.

Preserve supported file modes, symlink/gitlink semantics, path bytes, newline behavior, binary content, and existing Git objects/signatures when kept verbatim. Transformed commits have new identities; do not pretend old signatures still authenticate them.

### 18.4 Optimistic integration, not mandatory file locks

Prepare objects and validate candidates outside the publication lease. Update a protected ref against its expected head through an actual supported conditional contract. If the target moves, refresh/reintegrate/revalidate. A local Git `update-ref` expected-old-value check does not by itself make an arbitrary remote REST API CAS-capable. Verify the chosen transport semantics. [R13]

GitHub may merge, squash, or rebase according to its configuration. The gateway must import the actual accepted result and verify the tree/evidence relationship, not assume its submitted commit OID became `main`. Native SCV semantic solvers do not automatically execute inside GitHub.

### 18.5 Durable outbox and reconciliation

Persist operation ID, source candidate, intended refs, export policy, prepared Git OIDs, expected upstream state, and observed result. A timeout after push triggers read-back, not blind duplicate publication. Webhooks are hints; authenticated delivery deduplication plus periodic authoritative reconciliation handles lost/repeated events.

SCV persistence and GitHub publication are not one atomic transaction. Failed or uncertain publication remains recoverable state. Native metadata backups are required because GitHub source commits alone do not preserve all local drafts, conflicts, aliases, or provenance.

### 18.6 Sparse/offline safety

An offline manifest pins the requested source and reconstruction closure, required schemas/policies/aliases, and relevant parser/tool inputs if offline validation is promised. A sparse missing file is not a deleted file. A missing reference search result is not proof of no callers.

Thin, hybrid, and full-replica clients share semantics but advertise different completeness. Revoking server permission cannot retract previously downloaded offline bytes; confidentiality design must account for that limitation.

---

## 19. Compiler, build/test runner, context retrieval, and agents

### 19.1 Build and test integration

Builds consume immutable candidate snapshots, not live worktree fallback paths. Action keys include complete dependencies, compiler/toolchain IDs, target OS/ABI/CPU/features, static conditions, generated inputs, and relevant environment. Tree-sitter or a normalized source hash cannot independently authorize skipping compilation.

Source edits use source validators. Data-only updates use schema/constraint validators and relevant application tests. Configuration changes validate effective settings and affected build/runtime configurations. A mixed source/schema migration validates a combined candidate rather than validating isolated files and assuming compatibility.

Test observations are immutable and distinct from expectations. Store exact test definition, source revision, configuration, attempt, execution completion, and actual outcomes. No missing result becomes pass, and a passing configuration does not erase failures on another configuration.

### 19.2 LLM context and Repoformer

Keep one revision-bound context service over source entities, DB schema/data roles, requirements, tests, and history. Prefer exact references and lexical/graph retrieval; use embeddings/learned rerankers only when their measured value exceeds cost. Pack complete structural units or explicit partial projections, not unrelated arbitrary token chunks.

Repoformer is a reference for selective repository-completion retrieval, not evidence that an SCV issue-solving workflow will obtain the same gains. Reproduce its pinned baselines, then compare no-retrieval, always-retrieve, graph-selective, deterministic-selective, and optional learned policies on held-out SCV tasks. [R14]

Mandatory validation and policy context cannot be skipped by a learned retrieval policy. Context bundles identify exact source/schema revisions, content spans, permissions, tokenizer/policy versions, omissions, and completeness. Do not index future solution commits into historical evaluation contexts.

### 19.3 Agent isolation and proposed edits

Each agent receives a separate workspace/overlay or an explicitly coordinated shared transaction. Shared caches are immutable; source buffers are not shared mutable scratch space. Capture tool execution receipts and edits, not just terminal transcripts.

Tie Feature/Task/Change/Run/Context/Proposal/Evidence identities together using existing lifecycle objects. Runs are attempts, not durable logical tasks. A stopped run retains acknowledged private work. Agent input from repository text remains data and cannot grant plugin permissions or publication authority.

---

## 20. Module ownership and integration plan

Prefer small facades and adapters around existing modules. Proposed paths below are ownership suggestions, not claims that those files exist.

| Capsule | Existing anchors | Proposed work |
|---|---|---|
| SDN configuration | Shared SDN parser/strict types and serialization | `scv/config/`: schemas, effective policy, routes, profile/lock loader. |
| Plugin host | Parser registry/lock/session and existing native/plugin infrastructure | `scv/providers/`: capabilities, ABI envelopes, sandbox/worker execution, result validation. |
| Shared conflict model | Source conflicts and `db_conflict_*` modules | Versioned domain-tagged conflict envelope; adapters preserve richer existing payloads. |
| Source solvers | `identity*`, `structural_match`, `refactoring_relations`, `region_merge`, `merge*` | `scv/solve/source/`: wrappers first, revision-aware identity and semantic validation next. |
| DB schema | `db_schema`, `db_patch`, canonical codec | `scv/db_schema_v2/`: ColumnUid, typed migrations, old-schema adapters. |
| DB value solvers | `db_reducer`, `db_remove_wins`, paged DB paths | `scv/solve/database/`: policy-bound deterministic adapters, transaction constraints. |
| Identity/settlement | `distributed_identity*`, `db_allocation`, receipts/admission | Extend existing IDs and candidate planning; authoritative read-back and epoch fencing. |
| Capture | `editor_ipc`, `nvim_protocol`, events/coalescer/journal | Unified typed operation batches, host/OS/editor/agent adapters. |
| Hashing | Shared crypto/hash and runtime paths | Shared purpose/provider facade, XXH3/GXHash/BLAKE3 conformance and migration. |
| Storage | `store`, CST IR, packs, integrity, GC | Lossless node/row records, representation catalog, structural packing and closure walkers. |
| Build/context | `compile_snapshot`, invalidation, evidence/lifecycle | Exact candidate validation, shared scheduler/indexes, selective context. |
| Gateway | Backend adapters, public/network remote, sj coordination | Native RPC, object service, durable outbox, Git mapping, authority-specific settlement. |
| Recovery/testing | Existing restore drills and migration scripts | New format/provider/domain tests, cross-host crash/retry/partition drills. |

An SCV solver must not import the whole compiler, test runner, or network stack merely to implement a pure merge rule. Validators request those services through typed orchestration. The hash facade remains reusable by the compiler and OS without importing SCV.

Track four statuses separately for every capability: **source present**, **unit evidence**, **end-to-end execution evidence**, and **operational qualification**. A helper with simulated transport does not complete a real-network task.

## 21. Implementation backlog

### 21.1 Tracking and evidence rules

The following **65 tasks are proposed**. `SCVN-*` is a planning namespace, not a product version. Dependencies name the minimum accepted contracts; prototypes may run earlier, but integration completion requires their prerequisites and actual caller evidence. None of these rows is marked complete by this document.

Store the executable tracking data in the existing SDN work database. Each task needs an owner, requirement IDs from §1, design and SSpec links, an implementation revision, a required-check manifest, actual evidence receipts, resource observations, and a rollback note. Task status must distinguish source-only implementation from operationally verified behavior.

The plan deliberately reuses existing identity/allocation/reducer code. A rewrite of those foundations is not an acceptance condition; exposing their validated behavior through the new contracts is.

### B — Baseline and contracts

| Task | Deliverable | Depends on | Acceptance evidence |
|---|---|---|---|
| `SCVN-B01` | Refresh the pinned call graph, existing tests, provider inventory, and current authority policy. | — | Every capability has separate source/unit/integration/operational evidence; stale defects are not copied forward. |
| `SCVN-B02` | Specify domain-tagged objects, requests, results, version negotiation, errors, and canonical serialization. | `SCVN-B01` | Golden encodings and rejection fixtures cover every authority-bearing field and reference kind. |
| `SCVN-B03` | Harden typed reads, atomic publication, WAL ordering, and durability acknowledgements. | `SCVN-B01` | Read failures cannot become empty files; interrupted writes cannot produce acknowledged incomplete roots. |
| `SCVN-B04` | Map new requirements and the retained SCV3 backlog into the existing SDN work database. | `SCVN-B01`, `SCVN-B02` | Every task links requirements, design, SSpec, implementation, evidence, ownership, and rollback; no duplicate authoritative tracker. |

### C — SDN configuration

| Task | Deliverable | Depends on | Acceptance evidence |
|---|---|---|---|
| `SCVN-C01` | Implement bounded full-SDN loading plus versioned SCV schema validation. | `SCVN-B02` | Nested maps, inline arrays, and named tables parse through the correct entry point; duplicates, unknown mandatory keys, and malformed tables fail. |
| `SCVN-C02` | Implement role-aware routing and explicit overlap/rename policy. | `SCVN-C01` | The same .sdn extension routes correctly as configuration, schema, or data; old/new role changes cannot weaken policy. |
| `SCVN-C03` | Compute effective configuration with authority-policy intersection and exact digests. | `SCVN-C01` | Local/CLI settings cannot grant capabilities, weaken secure algorithms, or approve their own policy changes. |
| `SCVN-C04` | Define SDN provider manifests, profile files, and artifact lock generations. | `SCVN-C01`, `SCVN-C03` | Every executable dependency resolves to an approved artifact/ABI; no implicit install on capture. |
| `SCVN-C05` | Add typed SDN configuration and protected-policy solver adapters. | `SCVN-C02`, `SCVN-P01`, `SCVN-P04` | Disjoint preferences merge by schema; security changes are revalidated under the old accepted policy. |

### P — Provider host and conflict framework

| Task | Deliverable | Depends on | Acceptance evidence |
|---|---|---|---|
| `SCVN-P01` | Create parser/model/solver/validator/publisher interfaces and adapters for existing source/DB implementations. | `SCVN-B02`, `SCVN-C04` | Pure merge code is callable through one typed host contract without importing a compiler or network stack. |
| `SCVN-P02` | Implement bounded provider execution, artifact verification, sandboxing, cancellation, and safe ABI marshalling. | `SCVN-P01` | Denied clock/network/filesystem operations stay denied; crashes/timeouts preserve inputs and return explicit non-success. |
| `SCVN-P03` | Implement deterministic solver routing, composition, read/write-set checks, and exact-key caching. | `SCVN-P01`, `SCVN-C02`, `SCVN-C03` | No first-finished winner; overlapping candidate plans require an explicit composition rule or conflict. |
| `SCVN-P04` | Implement independent host validation and required-check manifests. | `SCVN-P01`, `SCVN-C03` | Solver claims cannot substitute for verified receipts; every required check has an exact subject and producer. |
| `SCVN-P05` | Persist domain-tagged conflicts, resolution receipts, and guarded resolution reuse. | `SCVN-P03`, `SCVN-P04`, `SCVN-B03` | Both sides survive failures; changed base/schema/policy/provider inputs invalidate cached decisions. |

### S — Source identity and solvers

| Task | Deliverable | Depends on | Acceptance evidence |
|---|---|---|---|
| `SCVN-S01` | Add revision-aware file/entity maps over all relevant parents, with explicit ambiguity. | `SCVN-B02`, `SCVN-B03` | Branching, competing moves, copies, and repeated identical declarations cannot collapse distinct identities. |
| `SCVN-S02` | Apply verified typed file/node/refactor operations with base and byte preconditions. | `SCVN-S01`, `SCVN-E01`, `SCVN-P01` | Move-plus-edit succeeds when compatible; stale bodies, forged operations, and unsupported semantics remain conflicts. |
| `SCVN-S03` | Wrap and extend structural three-way merging through pinned language profiles. | `SCVN-S02`, `SCVN-O01`, `SCVN-P03` | Ordered constructs retain order; only profile-authorized commutative contexts merge automatically. |
| `SCVN-S04` | Connect compiler/configuration-aware source validators and syntax-gated promotion. | `SCVN-S03`, `SCVN-R01`, `SCVN-R02` | Successful parsing alone never claims compilation; invalid local edits survive while protected promotion blocks. |
| `SCVN-S05` | Expose entity history, blame, selective undo, and reopenable conflict resolution. | `SCVN-S03`, `SCVN-P05` | Undo preserves unrelated later changes; uncertainty and multi-parent lineage stay visible. |

### D — Database schema

| Task | Deliverable | Depends on | Acceptance evidence |
|---|---|---|---|
| `SCVN-D01` | Introduce ColumnUid/TableUid schema records and versioned field-addressing codecs. | `SCVN-B02`, `SCVN-I01` | Rename/reorder preserve identity; drop-and-recreate gets a new identity; legacy name-based patches remain explicit v1. |
| `SCVN-D02` | Implement Add/Rename/Drop/Alter/Constraint schema operations and three-way schema solver. | `SCVN-D01`, `SCVN-P03` | Different compatible additions merge; same-name independently created columns do not silently coalesce. |
| `SCVN-D03` | Implement reviewed migration plans, old-schema adapters, lazy constant defaults, and compatibility checks. | `SCVN-D02` | Old-schema writes are mapped explicitly or refused; dynamic defaults/backfills are not invented during replay. |
| `SCVN-D04` | Implement SDN parsing/projection with stable row/column bindings and stale-base protection. | `SCVN-D01`, `SCVN-C01`, `SCVN-V01` | Manual edits produce typed patches from a pinned base; comments/order and raw submitted text remain recoverable. |

### V — Database values and constraints

| Task | Deliverable | Depends on | Acceptance evidence |
|---|---|---|---|
| `SCVN-V01` | Adapt the existing typed reducer, admission, and conflict records to the solver host. | `SCVN-P01`, `SCVN-D01` | Existing scalar/list/set/authority rules retain behavior; preview remains distinct from admission. |
| `SCVN-V02` | Version field semantics for scalar, ordered list, observed/remove-wins sets, counters, and immutable observations. | `SCVN-V01` | Only declared algebraic types commute; absent/null/default/explicit values remain distinguishable. |
| `SCVN-V03` | Implement incremental unique/FK/check constraint closure and transaction predicate validation. | `SCVN-V02`, `SCVN-D02` | Write-skew and cross-row conflicts are detected at the accepted candidate, not only at individual edits. |
| `SCVN-V04` | Coordinate schema, data, references, and dependent source in one candidate envelope. | `SCVN-V03`, `SCVN-D03`, `SCVN-R02` | Either the required combined candidate is admitted or all constituent drafts remain unaccepted and recoverable. |
| `SCVN-V05` | Implement causal checkpoints, frontier-aware compaction, replica retirement, and old-client rejoin. | `SCVN-V02`, `SCVN-I01` | Tombstones/dots cannot be removed merely by age; retired clients resynchronize without resurrecting deleted state. |

### I — Identity and settlement

| Task | Deliverable | Depends on | Acceptance evidence |
|---|---|---|---|
| `SCVN-I01` | Harden actor-incarnation/counter creation, persistence, cloning, and restore behavior using existing identity types. | `SCVN-B02`, `SCVN-B03` | Counters cannot be reused after acknowledged creation; cloned/restored writers obtain a new incarnation when required. |
| `SCVN-I02` | Extend existing allocation planning to tables/columns and compact typed projections. | `SCVN-I01`, `SCVN-D01`, `SCVN-V03` | Aliases, high-water marks, references, and accepted candidate state are planned together; duplicate requests are idempotent. |
| `SCVN-I03` | Bind settlement receipts to the deployment authority and verified accepted-ref read-back. | `SCVN-I02`, `SCVN-G05`, `SCVN-G06` | No official alias is acknowledged from an unaccepted Git topic branch; races replan and lost acknowledgements reconcile. |
| `SCVN-I04` | Implement alias/reference completeness for offline and sparse replicas. | `SCVN-I02`, `SCVN-G03` | Unknown aliases and missing closure are not treated as absent entities; old epoch references remain resolvable or explicitly rejected. |

### H — Shared multi-hash

| Task | Deliverable | Depends on | Acceptance evidence |
|---|---|---|---|
| `SCVN-H01` | Implement shared purpose-typed provider selection, capability queries, and algorithm-tagged digest records. | `SCVN-B02`, `SCVN-C03` | Fast fingerprints cannot satisfy secure object parameters; actual selected algorithm is always observable. |
| `SCVN-H02` | Qualify shared Simple and official xxHash/BLAKE3 paths against upstream vectors and differential tests. | `SCVN-H01` | Full-length, empty, streaming, SIMD, and supported parallel paths agree; no short-input-only provider is registered for files. |
| `SCVN-H03` | Add optional GXHash with versioned output semantics, supported hardware checks, and truthful fallback. | `SCVN-H01` | Unsupported hardware either refuses or selects a different tagged algorithm; no invented portable/streaming equivalence. |
| `SCVN-H04` | Add one-read multi-hash scheduling, lazy secondary hashes, and explicit legacy SHA-256/secure alias migration. | `SCVN-H02`, `SCVN-H03`, `SCVN-B03` | Migration validates real bytes/closure; enabled algorithms are not all eagerly computed; legacy signed DB v1 payloads retain their meaning. |

### O — Structural storage

| Task | Deliverable | Depends on | Acceptance evidence |
|---|---|---|---|
| `SCVN-O01` | Implement pinned parser sessions and all-byte lossless extraction with full/incremental differential oracles. | `SCVN-P01`, `SCVN-B02` | Trivia, errors, anonymous tokens, gaps, injections, and unsupported inputs never lose or duplicate bytes. |
| `SCVN-O02` | Implement syntax node/block/sibling source layouts and schema/row/value DB layouts. | `SCVN-O01`, `SCVN-D01` | Every source boundary is structural; tiny records inline and giant indivisible units stream intact. |
| `SCVN-O03` | Implement collision-safe node DAGs, occurrence indexes, codecs, and indexed packs of complete records. | `SCVN-O02`, `SCVN-H02`, `SCVN-H04`, `SCVN-B03` | Repacking/recompression cannot alter raw identity; logical entities remain separate from shared byte nodes. |
| `SCVN-O04` | Extend integrity walkers, reachability, parser-free restore, and concurrent quarantined GC. | `SCVN-O03` | Required dictionaries, deltas, aliases, active readers, unresolved conflicts, and unexported roots survive GC. |
| `SCVN-O05` | Evaluate optional bounded structural deltas and raw-digest deferral as separately gated optimizations. | `SCVN-O04`, `SCVN-R03` | Benefits are measured; depth/closure/raw-digest status remain explicit; both optimizations default off. |

### E — Operation capture

| Task | Deliverable | Depends on | Acceptance evidence |
|---|---|---|---|
| `SCVN-E01` | Define verified operation batches, event IDs, origin tags, preconditions, and transaction completion semantics. | `SCVN-B02`, `SCVN-B03`, `SCVN-I01` | Intent, attempted action, observed effects, and accepted operation remain distinguishable; no failed move is replayed as success. |
| `SCVN-E02` | Integrate Simple OS committed filesystem events and supported host cp/mv/rename wrappers. | `SCVN-E01` | Copy gets a new identity; cross-volume moves, atomic saves, hardlinks, and partial failures reconcile correctly. |
| `SCVN-E03` | Complete actual IDE/editor IPC, transport ABI, buffer revisions, and multi-file refactor transactions. | `SCVN-E01`, `SCVN-P02` | Native transport executes end to end; stale editor generations and incomplete transactions cannot silently publish. |
| `SCVN-E04` | Integrate Caret/Spipe/LLM tool mutation capture and independent effect verification. | `SCVN-E01`, `SCVN-E03` | Proposed commands are not accepted as executed effects; private transcript capture stays optional. |
| `SCVN-E05` | Implement trustworthy watcher cursors, overflow/restart reconciliation, and frozen multi-file capture. | `SCVN-E01`, `SCVN-B03` | Same-size/mtime edits and missed events cannot report false clean; unavailable hooks trigger correct fallback. |
| `SCVN-E06` | Add safe coalescing, batching, queue backpressure, origin filtering, and checkpoint durability accounting. | `SCVN-E02`, `SCVN-E03`, `SCVN-E04`, `SCVN-E05` | No per-keystroke commit/build loop; coalescing preserves causal/observed boundaries and acknowledged effects. |

### R — Runtime, evidence, and agents

| Task | Deliverable | Depends on | Acceptance evidence |
|---|---|---|---|
| `SCVN-R01` | Integrate immutable source/DB/config candidates with compiler and build/test inputs. | `SCVN-B02`, `SCVN-E05` | No live-worktree fallback; target/toolchain/static-condition differences prevent invalid cache reuse. |
| `SCVN-R02` | Produce and verify complete exact-candidate validation/approval receipts. | `SCVN-P04`, `SCVN-R01` | Missing, stale, incomplete, skipped, and forged results cannot satisfy protected policy; observations differ from expectations. |
| `SCVN-R03` | Share scheduler, derived-data cache, memory budgets, and short publication critical sections. | `SCVN-P03`, `SCVN-E06`, `SCVN-R01` | One capture feeds consumers; no nested thread-pool explosion or expensive computation under the ref lease. |
| `SCVN-R04` | Integrate isolated agent workspaces, task/change/run identities, cancellation, and recovery. | `SCVN-S01`, `SCVN-E06`, `SCVN-R02` | Concurrent agents retain independent changes; cancellation cannot erase acknowledged drafts. |

### G — Native gateway and Git

| Task | Deliverable | Depends on | Acceptance evidence |
|---|---|---|---|
| `SCVN-G01` | Implement checkout-free local/native RPC over exact immutable identities and bounded batches. | `SCVN-P01`, `SCVN-B03`, `SCVN-C03` | SCV-only callers can query source/schema/history with explicit authorization and completeness. |
| `SCVN-G02` | Implement actual authenticated cross-host transport, quotas, verification, and resumable object transfer. | `SCVN-G01`, `SCVN-H02` | Real-host disconnect/substitution/authentication tests pass; filesystem simulation is insufficient. |
| `SCVN-G03` | Implement local/shared draft replication, offline pins, thin/hybrid/full modes, and durable receipts. | `SCVN-G02`, `SCVN-O04` | Private revisions survive disconnection; fetched caches and sole local copies have different eviction rules. |
| `SCVN-G04` | Implement faithful Git import/export, revision projection mapping, and Git/jj adapter read-back. | `SCVN-G01`, `SCVN-H04`, `SCVN-O03` | Bytes/modes/parents are verified; original imported Git objects remain preserved where applicable; private snapshot parents do not leak. |
| `SCVN-G05` | Implement durable publication outbox, topic branch/PR integration, and explicit expected-state updates. | `SCVN-G02`, `SCVN-G04`, `SCVN-R02` | A lost push response cannot duplicate or overwrite publication; Git REST force=false is not mislabeled as strict old-OID CAS. |
| `SCVN-G06` | Reconcile upstream landing, merge/squash/rebase identities, policy evidence, and authority generations. | `SCVN-G05` | Actual landed tree/commit is imported; a topic branch or stale check never proves protected acceptance. |
| `SCVN-G07` | Add gateway-native backups, independent mirrors, failover fencing, and restore/read-only disaster mode. | `SCVN-G03`, `SCVN-G06`, `SCVN-I03` | Recovery preserves native metadata, accepted aliases, and drafts not contained in Git; split authority cannot acknowledge conflicting settlements. |

### Q — Context and evaluation

| Task | Deliverable | Depends on | Acceptance evidence |
|---|---|---|---|
| `SCVN-Q01` | Extend exact ContextBundle retrieval across source entities, schema/data roles, requirements, and evidence. | `SCVN-G01`, `SCVN-D04`, `SCVN-R02` | Permissions, revision/schema versions, token budget, and omitted/missing context are explicit. |
| `SCVN-Q02` | Reproduce Repoformer baselines and compare bounded selective retrieval on held-out SCV tasks. | `SCVN-Q01`, `SCVN-S05`, `SCVN-R04` | Model/data/code pins and actual verified task outcomes are recorded; no upstream speedup is claimed for SCV. |

### M — Qualification and rollout

| Task | Deliverable | Depends on | Acceptance evidence |
|---|---|---|---|
| `SCVN-M01` | Implement dual readers, shadow solvers/new representations, and old-policy/new-policy migration previews. | `SCVN-C05`, `SCVN-S04`, `SCVN-V04`, `SCVN-H04`, `SCVN-O04` | Old source and DB data restore unchanged; new plans are compared without changing acceptance authority. |
| `SCVN-M02` | Run differential, crash, corruption, concurrency, causal-replay, and real-network campaigns. | `SCVN-M01`, `SCVN-I03`, `SCVN-G06`, `SCVN-R04` | All declared scenarios actually execute; failures/unavailable hardware remain explicit, with reproducible evidence. |
| `SCVN-M03` | Enable scoped local and gateway deployments with measured budgets and tested rollback. | `SCVN-M02` | Users can disable new writers/solvers without losing acknowledged work or requiring incompatible old readers. |
| `SCVN-M04` | Authorize redundant representation reclamation and bounded journal/causal compaction. | `SCVN-M03`, `SCVN-V05`, `SCVN-O04`, `SCVN-G07` | Independent restore succeeds after deletion of redundant copies; unresolved/offline references cannot become dangling. |
| `SCVN-M05` | Evaluate native protected-ref authority as a separate decision under retained migration gates. | `SCVN-M03`, `SCVN-G07`, `SCVN-I04` | Existing cutover requirements and new protocol/security/recovery gates have independent evidence; no date-driven promotion. |

### 21.2 First complete vertical slice

Start with one local source fixture and one SDN database fixture, not a distributed rewrite. Load genuine SDN configuration, select a pinned built-in source or DB adapter through the provider host, preserve all input bytes, create a candidate, run independent validators, and record a typed conflict or accepted local result.

The source fixture is a verified file move on one branch plus an independent function-body edit on another. The DB fixture is two offline column additions, followed by a rename and an old-schema row update. The slice must demonstrate that the same orchestration applies **different semantic rules**, and that a conflict cannot disappear by switching to a generic line solver.

Only after that local contract is proven should the gateway add actual synchronization, authoritative alias settlement, and Git publication. Plugin breadth, native remote authority, and learned solvers must not delay a correct useful local implementation.

---

## 22. Parallel delivery waves and prior-plan crosswalk

### 22.1 Delivery waves

Waves group work, not elapsed-time promises. The dependency graph in §21 governs integration when a task spans waves.

| Wave | Work focus | Parallel ownership | Exit condition |
|---|---|---|---|
| W0 — Baseline and schemas | B01–B04, C01–C04 | Source audit, SDN schemas, canonical contracts, fixtures | Correct parser entry point, authority model, reference formats, and recovery baseline are agreed. |
| W1 — Domain separation | P01–P04, D01, V01, H01–H03, O01 | Provider host, DB schema/reducer adapters, hash/parsing | Source and database requests route differently through real adapters; untrusted output cannot self-admit. |
| W2 — Local correctness | S01–S03, D02–D04, V02/V03, E01–E05, O02/O03 | Source identities, schema evolution, editor/OS capture, storage | Both local vertical fixtures preserve bytes and produce correct typed conflicts/candidates. |
| W3 — Evidence and durability | C05, P05, V04, E06, R01–R04, H04, O04 | Validation, batching, compiler/test integration, restoration | Invalid work remains recoverable; complete exact-candidate evidence governs promotion; parser-free restore succeeds. |
| W4 — Real gateway | G01–G06, I01–I04 | Native RPC, transport, Git projection, settlement | Cross-host clients use SCV only; retries and upstream races cannot falsely acknowledge acceptance or aliases. |
| W5 — Qualification | V05, G07, M01/M02, S05, Q01/Q02 | Recovery, causal retention, context evaluation, differential campaigns | Required suites execute with measured overhead and independent recovery; no known silent-loss/false-clean case remains in the corpus. |
| W6 — Controlled adoption | M03/M04; optional O05 | Scoped rollout and measured compression/retention improvements | Rollback, offline rejoin, and representation reclamation are proven for the deployed formats. |
| W7 — Separate authority decision | M05 | Existing migration/cutover owners | Retained authority gates and new protocol gates are independently satisfied; otherwise stay Git-authoritative. |

I01 can be developed in W1; W4 groups its authoritative cross-host integration. Likewise, R01/R02 contracts should be mocked early with explicitly non-production fixtures, then replaced by actual execution evidence before dependent tasks close.

### 22.2 Previous 61-task plan: retained objectives and new owners

This document consolidates the prior `SCV3-*` plan rather than silently deleting its requirements. The mapping is at workstream level; B04 must record task-to-task links in SDN. A mapped task is not automatically complete.

| Previous workstream | Retained objective | New primary owners / extension |
|---|---|---|
| SCV3-B01–B03 | Baseline, canonical formats, safe I/O | SCVN-B01–B04; domain and SDN contracts are explicit. |
| SCV3-H01–H07 | Purpose typing, official vectors, ISA, migration, collision tests | SCVN-H01–H04; adds GXHash and multi-hash policy. Replace the obsolete 64-byte BLAKE3 finding with current conformance qualification. |
| SCV3-P01–P06 | Pinned providers, lossless parsing, native semantics, resource safety | SCVN-C04/P01/P02/O01/O02/S04; parser and solver responsibilities are separate. |
| SCV3-S01–S08 | Node DAG, structural boundaries, codecs/packs, GC and optional deltas | SCVN-O01–O05/M04; extends logical units to database records without forcing source merge rules onto them. |
| SCV3-X01–X05 | One capture, correct watcher reconciliation, derived services and caches | SCVN-E01–E06/R03/G01/G03; explicit operation provenance and durability windows. |
| SCV3-D01–D06 | Unified edit graph, lineage, patches, merge, Git patch fidelity, history/undo | SCVN-S01–S05/P03/P05/G04; same input graph supports raw/structural/entity views. |
| SCV3-Q01–Q05 | Exact context, graph/lexical selection, Repoformer reproduction | SCVN-Q01/Q02; includes schema/data roles and policy context. |
| SCV3-A01–A05 | Agent isolation, lifecycle, protected mutation, fencing and Caret/Spipe | SCVN-R04/E04/I03/G05/G06; no mandatory source-file locking. |
| SCV3-E01–E05 | Build keys, exact evidence, impacted tests and requirement traceability | SCVN-R01/R02/B04/Q01; DB-specific validation is distinct from compilation. |
| SCV3-R01–R05 | Git/jj capabilities, real RPC, resumable transport, sparse/shared services | SCVN-G01–G07/I04; gateway is first-class but thin mode is optional. |
| SCV3-M01–M06 | Shadow writes, recovery, hashes, raw reclamation, authority gates | SCVN-M01–M05; adds provider, DB-schema, alias, and causal-epoch migrations. |

All old byte-round-trip, upstream-vector, parser-error, permission, stale-evidence, concurrency, and recovery tests remain required unless replaced by a demonstrably equivalent stronger case. New tests in §23 extend them; a renamed test is not an evidence reset.

### 22.3 Parallel-agent development rules

Allocate one owner for shared contracts, configuration policy, identity codecs, and publication state machines. Other lanes submit narrow contract proposals rather than independently changing these formats. Give each lane an isolated worktree and stable fixture set. Integrate small vertical slices with a real caller, not helper-only implementations.

Keep rename-only refactors separate from behavior changes. Every format/provider update includes compatibility tests and source-level documentation. Update Spipe skills, guides, and LLM knowledge references when an interface or safety invariant changes; obsolete guidance must be marked superseded rather than left as competing instructions.

---

## 23. Acceptance tests and CI

### 23.1 Test interpretation

These are **planned scenarios**, not results observed in this document. Each scenario becomes an SSpec/system test or a property/fault campaign with a reproducible manifest. A test that only prints a command, checks a file exists, or returns `pass` without executing its subject is not acceptance evidence.

Native SDN examples must be parsed by the actual selected Simple SDN implementation, schema-checked, and round-tripped before release. A Python/YAML parser accepting similar syntax is not a substitute.

The matrix contains **87 acceptance scenarios**. Each scenario may contain many generated cases; the scenario count is not a claim about executed test counts.

| Scenario | Required outcome | Primary tasks |
|---|---|---|
| `AT-C01` | Parse all shipped .sdn configs/profiles/manifests with bounded full SDN; nested maps, inline arrays using =, and named tables work. | `SCVN-C01`, `SCVN-C04` |
| `AT-C02` | Duplicate keys, wrong table widths, unsupported mandatory fields, malformed scalars, and byte/depth/node limits reject precisely without changing the last accepted config. | `SCVN-C01` |
| `AT-C03` | Route identical .sdn extensions as config, schema, and data; ambiguous matches and protected-file renames cannot silently select a weaker solver. | `SCVN-C02`, `SCVN-C05` |
| `AT-C04` | A branch that changes its solver/policy cannot use that proposed policy to approve itself; local or CLI overrides cannot enable denied capabilities. | `SCVN-C03`, `SCVN-C05` |
| `AT-C05` | An artifact/ABI/query/profile upgrade changes the effective derivation key; restoring historical raw bytes does not require the upgraded provider. | `SCVN-C04`, `SCVN-O04` |
| `AT-P01` | Missing required plugin blocks verified promotion but not ordinary save/private checkpoint; DB solver absence never falls back to an accepting text merge. | `SCVN-P01`, `SCVN-P03` |
| `AT-P02` | A solver attempts network access, live-file writes, shell execution, clock/random input, or alias allocation; the host denies the operation. | `SCVN-P02` |
| `AT-P03` | Crash, timeout, cancellation, oversized output, malformed result, and cyclic object references return explicit failure/partial states without publishing. | `SCVN-P02`, `SCVN-P04` |
| `AT-P04` | Two solvers propose overlapping edits or inconsistent mappings; the host detects the conflict instead of accepting whichever finishes first. | `SCVN-P03` |
| `AT-P05` | Same pinned inputs yield the same deterministic candidate under varied scheduling; resource-limited outcomes remain explicit and are not reusable successes. | `SCVN-P03`, `SCVN-R03` |
| `AT-P06` | A solver forges validation receipts or says all checks passed; independent producer/subject/required-manifest checks reject it. | `SCVN-P04`, `SCVN-R02` |
| `AT-P07` | A stored manual resolution is reused only with valid base/entity/schema/policy/provider bindings; changed preconditions force revalidation. | `SCVN-P05` |
| `AT-S01` | Move a file on one side and edit an unchanged function on the other; preserve file/entity identity and both intended effects. | `SCVN-S01`, `SCVN-S02` |
| `AT-S02` | Copy, competing rename, rename-delete, and repeated identical declarations do not collapse unrelated identities or lose a branch. | `SCVN-S01`, `SCVN-S03` |
| `AT-S03` | Merge histories with multiple relevant parents or ambiguous base ancestry; no first-parent shortcut erases relevant lineage. | `SCVN-S01`, `SCVN-S03` |
| `AT-S04` | Formatter changes and independent syntax-node changes align without dropping comments/directives or changing ordered constructs. | `SCVN-S03` |
| `AT-S05` | Side-effecting imports, macros/static conditions, and signature/caller incompatibility cannot be accepted solely because syntax parses. | `SCVN-S03`, `SCVN-S04` |
| `AT-S06` | Empty files, binaries, NUL-containing payloads, invalid UTF-8, and no-final-newline inputs survive generic storage; source-only validators do not govern all domains. | `SCVN-O01`, `SCVN-S04` |
| `AT-S07` | Invalid temporary code is saved and checkpointed; verified promotion/build selection blocks under policy without deleting or rewriting the private bytes. | `SCVN-S04`, `SCVN-E06` |
| `AT-S08` | Selective undo of a prior logical change preserves unrelated later edits or raises a typed conflict. | `SCVN-S05`, `SCVN-P05` |
| `AT-E01` | A failed cp/mv command or an agent command merely constructed but not executed cannot become a verified operation. | `SCVN-E01`, `SCVN-E02`, `SCVN-E04` |
| `AT-E02` | Atomic-save replacement, case-only rename, cross-volume copy/delete, hardlinks, and reused inode/file IDs are handled without false logical identity. | `SCVN-E02`, `SCVN-E05` |
| `AT-E03` | A real editor connection applies versioned edits/refactors end to end; stale buffers and disconnected half-transactions remain incomplete. | `SCVN-E03` |
| `AT-E04` | Unsupported editor/LLM tool or absent OS hook falls back to byte capture and conservative inference, not missing changes. | `SCVN-E04`, `SCVN-E05` |
| `AT-E05` | Same-size/same-mtime edits, dropped/reordered events, watcher overflow, and restart trigger correct reads/reconciliation. | `SCVN-E05` |
| `AT-E06` | A burst of fine-grained edits is coalesced without one durable revision/build per keystroke; acknowledged intermediate checkpoints are not erased. | `SCVN-E06` |
| `AT-E07` | Build outputs, SCV metadata, and DB projections do not cause build/commit feedback loops or bypass source-change detection for real edits. | `SCVN-E06`, `SCVN-R01` |
| `AT-E08` | Queue overload/disk-full returns an honest capture/durability state; a successful editor save is not falsely acknowledged as a durable SCV checkpoint. | `SCVN-E06`, `SCVN-B03` |
| `AT-D01` | Concurrent additions of different compatible columns merge by stable ColumnUid, irrespective of textual header order. | `SCVN-D01`, `SCVN-D02` |
| `AT-D02` | Independent same-name same-definition columns remain duplicate-intent candidates until an explicit equivalence/migration rule approves coalescing. | `SCVN-D02` |
| `AT-D03` | Same-name different-type/default/constraint additions yield a schema conflict; no timestamp winner or inferred coercion is selected. | `SCVN-D02` |
| `AT-D04` | Column rename/reorder plus row update resolves by ColumnUid; drop/recreate with the same name cannot resurrect old values. | `SCVN-D01`, `SCVN-D03` |
| `AT-D05` | An old-schema writer adds data after migration; explicit adapter succeeds or admission refuses with preserved draft. | `SCVN-D03` |
| `AT-D06` | Absent, null, defaulted, explicitly set, and tombstoned values remain distinct; volatile defaults are not reevaluated on each replica. | `SCVN-D03`, `SCVN-V02` |
| `AT-D07` | Adding a constant-default column avoids rewriting every historical row; old snapshots retain their original schema interpretation. | `SCVN-D03`, `SCVN-D04` |
| `AT-D08` | Manual SDN edits with missing/duplicate identity bindings or stale projection revisions cannot shift values into the wrong columns. | `SCVN-D04` |
| `AT-V01` | Disjoint column edits merge; incompatible scalar edits remain visible alternatives; wall-clock order never silently resolves them. | `SCVN-V01`, `SCVN-V02` |
| `AT-V02` | Observed/add-wins/remove-wins sets behave according to the selected versioned rule under duplicates and arbitrary causal delivery order. | `SCVN-V02`, `SCVN-V05` |
| `AT-V03` | Increments and append-only observations are not lost by scalar-style coalescing; replaying an operation cannot apply it twice. | `SCVN-V02`, `SCVN-E06` |
| `AT-V04` | Two individually valid transactions violate a shared unique, foreign-key, or cross-row constraint together; admission detects the combined violation. | `SCVN-V03` |
| `AT-V05` | A schema/data/source migration publishes only the validated combined candidate; failed validation does not partially settle its constituents. | `SCVN-V04`, `SCVN-R02` |
| `AT-V06` | Field merge-policy change races with old-policy operations; the migration policy handles the race explicitly, not by reinterpretation. | `SCVN-D03`, `SCVN-V02` |
| `AT-V07` | A generated SDN projection is reparsed for round-trip agreement; formatting/comment treatment remains explicit and submitted text remains recoverable. | `SCVN-D04`, `SCVN-O01` |
| `AT-I01` | Counter reservation, power loss, filesystem rollback, and cloned workspace cannot reuse an acknowledged actor-incarnation/counter identity. | `SCVN-I01` |
| `AT-I02` | Wall-clock rollback/skew and matching timestamps neither collide identities nor decide conflict winners. | `SCVN-I01`, `SCVN-V01` |
| `AT-I03` | Two gateway candidates allocate competing sequence values; only the accepted candidate is final, and the loser replans against the new map. | `SCVN-I02`, `SCVN-I03` |
| `AT-I04` | Retry a previously accepted batch: return the same mappings; reuse its ID with a different payload: reject rather than alias another operation. | `SCVN-I02`, `SCVN-I03` |
| `AT-I05` | A Git topic branch receives tentative aliases but never lands; clients cannot observe those numbers as final accepted IDs. | `SCVN-I03`, `SCVN-G06` |
| `AT-I06` | Acceptance succeeds and the reply is lost; authoritative read-back recovers the exact accepted candidate and aliases before acknowledgement. | `SCVN-I03`, `SCVN-G06` |
| `AT-I07` | Stale gateway fences/epochs, unknown aliases, and sparse missing references fail explicitly; alias numbers are never reused for another entity. | `SCVN-I04`, `SCVN-G07` |
| `AT-I08` | Compaction with a long-offline writer retains needed causal metadata, or requires an explicit retired-replica resync; deleted state cannot resurrect. | `SCVN-V05`, `SCVN-I04` |
| `AT-H01` | Official XXH3/BLAKE3 vectors and randomized large inputs match the selected implementation; zero input and valid zero-valued digests are not errors. | `SCVN-H02` |
| `AT-H02` | Lengths around 64-byte and 1024-byte boundaries, unaligned input, and arbitrary supported streaming partitions match one-shot results. | `SCVN-H02`, `SCVN-H04` |
| `AT-H03` | Force each available SIMD/scalar path; results agree. Unsupported ISA/provider requests refuse before execution or select a truthfully tagged supported algorithm. | `SCVN-H02`, `SCVN-H03` |
| `AT-H04` | GXHash major/version/seed/output distinctions are persisted for reusable fingerprints; no fixed-input-size/streaming capability is guessed. | `SCVN-H03` |
| `AT-H05` | Inject XXH3/GXHash collisions for unequal canonical bytes; deduplication, equality, and build caches retain distinct objects. | `SCVN-H01`, `SCVN-O03` |
| `AT-H06` | Multi-hash selection feeds only required/lazy consumers from one capture; failure of a secure provider never silently substitutes a noncryptographic result. | `SCVN-H04` |
| `AT-H07` | Legacy DB SHA-256 v1 signatures/digests remain verifiable after v2 registration; migration does not alter old canonical signed payloads. | `SCVN-H04`, `SCVN-M01` |
| `AT-O01` | All-byte coverage handles punctuation, trivia, BOM, CRLF, errors, missing nodes, and injected-language overlap without omission or duplication. | `SCVN-O01` |
| `AT-O02` | Full and incremental extraction agree after edits that change token spelling/trivia without large structural changed ranges. | `SCVN-O01` |
| `AT-O03` | Every new parsed-source boundary is a complete node/block/sibling boundary; a giant indivisible token streams intact rather than becoming arbitrary chunks. | `SCVN-O02` |
| `AT-O04` | Sharing identical nodes across files/revisions does not merge logical entity identities; moving an occurrence updates only occurrence metadata as appropriate. | `SCVN-O03`, `SCVN-S01` |
| `AT-O05` | Codec/pack changes preserve raw bytes and logical IDs; whole-file BLAKE3 is not confused with a node-Merkle root. | `SCVN-O03`, `SCVN-H04` |
| `AT-O06` | Restore retained history with all parsers/indexes absent; required recipes, dictionaries, and delta bases alone suffice. | `SCVN-O04`, `SCVN-M04` |
| `AT-O07` | Malformed lengths, excessive decompression/reference expansion, cycles, corrupt payloads, and missing dictionaries reject before publication. | `SCVN-O04`, `SCVN-P02` |
| `AT-O08` | GC races active readers, new revisions, unresolved conflicts, and unpublished drafts without removing their sole reconstruction closure. | `SCVN-O04` |
| `AT-O09` | Optional delta/deferred-raw-digest mode obeys depth/verification limits and explicit readiness states; disabling it remains compatible with retained objects. | `SCVN-O05`, `SCVN-M03` |
| `AT-G01` | A real host with no Git installation creates/synchronizes SCV drafts and queries through the gateway. | `SCVN-G01`, `SCVN-G02`, `SCVN-G03` |
| `AT-G02` | Actual cross-host transfer survives interruptions and duplicate uploads, verifies secure object identities, and enforces authorization on cache hits. | `SCVN-G02` |
| `AT-G03` | Disconnect, create local revisions, restart, edit again, and reconnect after upstream advancement without lost work or silent overwrite. | `SCVN-G03`, `SCVN-G06` |
| `AT-G04` | Sparse/unhydrated files are never exported as deletions; an incomplete reference query cannot report complete zero results. | `SCVN-G03`, `SCVN-I04` |
| `AT-G05` | Git round trips preserve supported bytes, modes, symlinks, path semantics, parent projections, and original imported objects where applicable. | `SCVN-G04` |
| `AT-G06` | A publication response is lost or an external writer advances the target; read-back/reconciliation prevents duplicate or stale acceptance. | `SCVN-G05`, `SCVN-G06` |
| `AT-G07` | GitHub merge/squash/rebase produces a new landed identity; the gateway imports the actual result rather than equating it to the submitted head. | `SCVN-G06` |
| `AT-G08` | Private checkpoints and sensitive native metadata do not leak through public Git ancestry, trailers, or automatic draft export. | `SCVN-G04`, `SCVN-C03` |
| `AT-G09` | Gateway failure/restore preserves settled aliases and unexported drafts using native backup; Git-only restore advertises its limitations. | `SCVN-G07` |
| `AT-R01` | Compiler/tests use a frozen candidate; changed OS/CPU/ISA/static settings/dependencies/toolchain invalidate incompatible cache results. | `SCVN-R01`, `SCVN-R03` |
| `AT-R02` | Required-check manifests distinguish not-run/skipped/incomplete/unavailable/cancelled/fail; a passing subset is never complete evidence. | `SCVN-R02` |
| `AT-R03` | Schema-only and data-only changes select DB validation, while mixed migrations include necessary source/application checks. | `SCVN-V04`, `SCVN-R02` |
| `AT-R04` | Concurrent isolated agents edit overlapping source and DB entities; all acknowledged drafts survive, with deterministic or explicit-conflict reconciliation. | `SCVN-R04` |
| `AT-Q01` | Each context item reconstructs at its declared revision/schema and permission scope; mandatory evidence cannot be omitted by a learned policy. | `SCVN-Q01` |
| `AT-Q02` | Repoformer/selective baselines use pinned held-out tasks without future-code leakage and report actual outcomes plus policy/token/time cost. | `SCVN-Q02` |
| `AT-M01` | Crash at each new object/WAL/map/ref/receipt boundary yields a complete old/new state or explicit corruption, never vacuous success. | `SCVN-M02`, `SCVN-B03` |
| `AT-M02` | Legacy and new shadow representations/solvers are compared without changing protected authority; unknown mandatory formats fail precisely. | `SCVN-M01` |
| `AT-M03` | Rollback with later acknowledged drafts retains compatible readers or performs verified export; it does not delete .scv to erase uncertainty. | `SCVN-M03` |
| `AT-M04` | Parser-free object-only restore, upstream-only limited restore, checkpoint restore, corrupt-index rebuild, missing-index recovery, and interrupted-transaction recovery are independently exercised. | `SCVN-M02`, `SCVN-G07` |
| `AT-M05` | Tombstone/alias/journal retention and raw-copy reclamation are tested with offline rejoin and independent restore before irreversible deletion. | `SCVN-M04`, `SCVN-V05` |

### 23.2 CI tiers and honest execution status

**Local/pre-commit:** bounded SDN parser/schema tests, affected canonical-codec and pure-reducer cases, provider manifest/routing validation, selected round trips, and no-vacuous-pass checks. Do not reparse the whole repository or invoke an LLM on every save.

**Every relevant pull request:** changed-domain acceptance fixtures, native caller integration, source/DB differential cases, hash vectors for available providers, stale-policy/precondition checks, real IPC tests, and selected crash/retry tests. Required hardware/platform cases are listed explicitly; unavailable execution is `not_run`, not pass.

**Scheduled/release qualification:** long edit/schema histories, 2/8/32-client concurrency, power-loss/crash boundaries, GC races, old-replica rejoin, corruption/hostile-provider inputs, real cross-host transport, and full restore/export matrices. Cross-compilation is not evidence of executing a backend on that architecture.

**Authority promotion:** independent recoveries, format rollback, real upstream reconciliation, gateway failover/fencing, and the retained native-cutover program. This is a separate review, not a side effect of all unit tests passing.

The runner emits SDN receipts containing exact implementation/toolchain/configuration revisions, cases attempted, cases actually completed, outcomes, required-but-unavailable coverage, and artifact references. Third-party tools may produce JSON at their boundary; convert it through a checked adapter rather than creating a second native SCV configuration format.

### 23.3 Property and model checks

Useful properties include parser-free byte round trip; stable column identity under rename/reorder; no alias reuse; idempotent patch/settlement replay; source/DB solver equivalence to a full reference path; provider digest equivalence; and no-lost-update publication. For declared commutative data types, verify their actual algebra under supported causal preconditions; do not demand or assume commutativity for arbitrary source edits or scalar assignments.

Model-check the small alias-allocation/accepted-ref/receipt state machine and the publication outbox where practical. A proof about that model does not prove filesystem durability, sandbox isolation, or GitHub API behavior; those require execution-based failure tests.

---

## 24. Performance and conflict-reduction evaluation

### 24.1 Baselines and experimental controls

Compare the pinned current SCV, Git with relevant caching/sparse features disclosed, a supported jj/Git workflow, and new SCV variants. Scion is an architectural reference, not a runnable local benchmark. Do not assume jj inherently creates more conflicts; measure each tool against the same edit history and correctness oracle.

Keep repository versions, retained history, hardware, OS/filesystem, cache warmness, provider artifacts, thread/memory budget, operation coverage, and validation strength fixed. Disclose differing guarantees: a deferred raw digest is not the same workload as synchronous full-file secure verification.

| Variant | Isolated question |
|---|---|
| Native SCV, byte-only baseline | Cost of established capture/versioning without new syntax/schema solvers. |
| Source solver with and without captured operations | Benefit of explicit rename/refactor evidence versus inference alone. |
| Existing reducer versus plugin-host adapter | Dispatch/isolation overhead without changing DB semantics. |
| Name/position-oriented text merge versus UID/schema-aware merge | Avoided false conflicts and detected schema/data errors. |
| Direct secure hash versus fast prefilter plus secure hash | Whether an extra fast hash actually helps on the measured object sizes. |
| XXH3 versus supported GXHash | End-to-end candidate lookup cost including dispatch, equality checks, and fallbacks. |
| Structural DAG without codec, then each codec | Separate deduplication benefit from compression benefit and read amplification. |
| Eager schema backfill versus lazy constant defaults | Bytes rewritten, replay/migration cost, and read-time overhead. |
| Local execution versus gateway execution | Network, secure verification, scheduling, export, and acceptance costs. |
| No/always/selective/learned retrieval | Verified task success per token and elapsed time, including selection overhead. |

### 24.2 Correctness-oriented conflict measures

Report **false conflicts**, **false-clean merges**, unresolved genuine conflicts, explicit-intent capture coverage, and human resolution work separately. A solver that hides more conflicts by discarding one side is worse, not better.

Use an independent labeled corpus covering rename+edit, copy+edit, cross-file extraction, formatting, static configuration, competing API changes, duplicated declarations, simultaneous schema additions, column rename/drop/recreate, unique-key races, foreign-key delete/update, and old-schema writers.

A useful evaluation reports:

```text
false_conflict_rate = compatible cases unnecessarily blocked / compatible cases
false_clean_rate   = incompatible cases incorrectly auto-admitted / incompatible cases
recovery_rate      = acknowledged retained states recovered / acknowledged retained states tested
capture_coverage   = operations with verified intent / eligible observed operations
```

Publish denominators, unsupported cases, sampling policy, and confidence/variation. Zero observed false-clean cases in a finite corpus is a release criterion for that corpus, not a mathematical guarantee for all programs.

### 24.3 Overhead and growth accounting

Measure p50/p95/p99 for ordinary edit capture, durable checkpoints, schema/data patches, status, solver execution, promotion, context queries, restore, and upstream landing. Separate queueing, lock/lease hold time, network, provider startup, secure hashing, parsing, compilation, and tests.

Track peak RSS, allocations, mapped/decoded bytes, I/O reads/writes, actual object count, journal frames/fsyncs, parser invocations, compared candidate pairs, IPC/RPC count, and bytes sent. Account for native + Git coexistence and all replicas, aliases, tombstones, dictionaries, evidence, raw copies, and indexes.

The metadata estimate `events × encoded bytes per event` is only a lower-level accounting term. It excludes source objects, indexes, framing, replication, and durability overhead; never present it as total repository growth.

Set budget targets using measured baselines before promotion. Example config values such as 150 ms debounce and 256 MiB worker allowance are experiment inputs, not measured optimums or guaranteed universal limits. High-cost providers may be restricted to background/explicit analysis while low-cost pure rules remain interactive.

### 24.4 Complexity expectations

A new input must be read. Tree-sitter can reparse more than the exact edited bytes. Full-file standard secure hashing may remain linear in the changed file. Source structural matching requires bounded candidates. A column metadata addition should normally avoid a full-table rewrite, but adding a unique constraint or performing a type conversion can legitimately require a scan or backfill.

An incremental constraint index is reusable only with a valid schema/index-generation witness. If that witness is missing, either rebuild/scan or report unavailable; do not certify the constraint from an incomplete index.

Keep expensive work outside publication critical sections. Parallelize immutable preparation and recheck the expected authority state before acceptance. An unchanged policy-valid cached result can be reused; an old receipt for a different candidate cannot.

---

## 25. Migration, recovery, and rollout

### 25.1 Independent migration axes

Track configuration schema, provider ABI/artifacts, source representation, DB schema/patch format, hash namespace, replication protocol, and publication authority separately. Updating one does not implicitly upgrade the others.

In particular, adding a BLAKE3 provider does not rewrite signed SHA-256 DB v1 patches; adding solver plugins does not grant them publication authority; deploying a gateway does not make GitHub merely a mirror unless that authority change is explicitly approved.

### 25.2 Staged rollout

| Stage | Allowed change | Required safety condition |
|---|---|---|
| F0 — Inventory | Pin all current formats, schemas, providers, roots, aliases, and authority policies. | Verified independent backup and restore of current source and native metadata. |
| F1 — Read and inspect | New SDN config/schema readers, capability inspection, and dry-run routing. | Old accepted configuration still governs; unknown required features fail without affecting save. |
| F2 — Shadow candidates | Run new source/DB solvers and build new structural representations alongside old authority. | Compare output plans/bytes/constraints; do not auto-accept divergent results. |
| F3 — Scoped local adoption | Enable built-in solvers, typed schema operations, and bounded capture for selected workspaces. | Private data preserved; actual validators and rollback readers available. |
| F4 — Gateway drafts | Real SCV-native synchronization and remote draft durability. | Cross-host auth, integrity, interruption, and independent native backup verified. |
| F5 — Accepted settlement/export | Compact aliases and protected Git publication through explicit authority protocol. | Atomic candidate content plus authoritative accepted-ref/read-back receipts; races/retries tested. |
| F6 — Reclamation/optimization | Causal checkpoints, redundant raw-copy removal, optional deltas/caches. | Independent restore and offline-rejoin gates; no deletion of unique evidence/identity or source closure. |
| F7 — Optional native authority | Consider SCV-owned protected refs with Git mirroring. | Retained cutover policy and all new durability/protocol gates satisfied; never automatic. |

A repository may remain indefinitely at a useful earlier stage. Missing optional learned retrieval, GPU work, virtual filesystems, or advanced delta compression must not prevent a correct local/gateway workflow.

### 25.3 Compatibility and rollback rules

Write new identity-bearing formats only after compatible readers and export/recovery tooling are shipped. Keep versioned decoders for retained source and DB histories. A binary rollback that cannot understand a newly published format is not a rollback plan.

Provider upgrades create new lock generations and derived cache keys. Existing immutable outcomes retain their provider/semantic provenance; source restoration must not execute old merge plugins. Recomputing a historical DB state may require the historical reducer semantics or a retained materialized checkpoint and a verified migration path.

Rollback disables new writers or routing profiles through the accepted policy generation, restores/retains compatible readers, and reconciles every later acknowledged draft/publication. Never delete `.scv` once it contains unique work or mappings. Do not renumber settled aliases to make a rollback aesthetically sequential.

### 25.4 Recovery drills

Exercise at least these independent modes on isolated copies: upstream Git-only recovery with clearly stated native-history limitations; checkpoint plus Git; native object/metadata-only restore; corrupted mutable DB/index rebuild; all derived indexes missing; interrupted source/DB/alias/publication transaction; and gateway failure after upstream acceptance but before acknowledgement.

Add a parser-free restore with raw redundant copies absent, plus a causal checkpoint followed by old-replica rejoin. Verify actual bytes, schema interpretation, alias identity, refs, and receipt subjects. Run a representative real build/application validation from restored frozen input; integrity scanning alone is not the complete drill.

A recovery environment may intentionally enter read-only mode until authority epoch/fencing and receipts are reconciled. Serving verified source safely is preferable to guessing whether an unacknowledged settlement occurred.

---

## 26. Risk register and completion criteria

| Risk | Required mitigation / evidence |
|---|---|
| SDN examples accidentally interpreted as YAML or sent through flat-only config parser | Native SDN parser tests, explicit schema versions, actual table/array fixtures. |
| Extension-based routing gives DB content a source/text solver | Domain-role manifests, old/new path checks, no unsafe domain fallback. |
| Solver supplies both change and its own approval | Separate capabilities, independently verified required-check receipts, old accepted policy. |
| Generic schema logic silently matches columns by ordinal/name | Stable ColumnUid and explicit versioned migration bindings. |
| Config/policy merge expands permissions by union | Deny-by-default typed policy merge evaluated under existing authority. |
| An offline clone reuses actor counters | Durable incarnation/counter contract, clone/restore detection and fresh writer identity. |
| A candidate allocation is acknowledged before protected acceptance | Authority-specific linearization and exact accepted-ref read-back. |
| Two gateway writers accept conflicting aliases | Fencing/CAS and one logical settlement authority; candidate aliases are not final. |
| Timestamp winner drops legitimate concurrent values | Visible scalar conflicts and declared causal/type-specific rules. |
| Causal compaction resurrects deleted data | Frontier/membership proofs or explicit replica retirement plus resynchronization. |
| Hook capture is incomplete or lies about execution | Verify effects against bytes; watchers and wrappers remain evidence, not sole truth. |
| Aggressive syntax merge produces parseable but incorrect source | Native compiler/config/application validators, adversarial corpus, explicit partial claims. |
| Hash selection weakens integrity or changes outputs across CPU/provider | Purpose types, algorithm-specification tags, secure-policy intersection, upstream conformance. |
| Excessive nodes/events/aliases defeat compression | Coalescing, complete-record packing, compact references, bounded caches, measured total accounting. |
| GC deletes required recipes, causal state, aliases, or unexported work | Typed reference walkers, retained roots, quarantine, independent restore/rejoin gates. |
| Git publication bypasses native DB validation | Protected acceptance path or trusted required integration checks validate the combined projection and mapping. |
| Optional plugins force high startup/runtime overhead | Built-in pure adapters first, session-level dispatch, lazy workers, shared budgets. |

### 26.1 Definition of done by capability

**SDN configuration:** all native configurations, policies, manifests, and lockfiles use actual SDN syntax and tested versioned schemas; effective authority cannot be weakened by precedence or self-editing policy.

**Solver framework:** at least one actual source solver and one DB schema/value solver run through the shared host with domain-correct semantics, explicit unresolved outcomes, independent validation, reproducible provenance, and no side-effect/publication privilege.

**Database concurrency:** offline column/row creation, rename/reorder, schema migration, value merge, cross-row constraints, provisional identity, final alias settlement, retries, and old-client rejoin have executed acceptance evidence. A passing set-reducer unit test alone is insufficient.

**Source/event integration:** real OS/editor/agent execution paths provide verified operation evidence; unsupported paths fall back safely; invalid local work survives; revision-aware merges reduce measured false conflicts without known false-clean regressions in the required corpus.

**Storage/hash:** all-byte structural round trips, full hash conformance, truthful provider selection, legacy compatibility, and parser-free recovery are demonstrated; benchmark claims include coexistence and metadata costs.

**Gateway:** SCV-only clients synchronize with a real authenticated server; Git/GitHub publication and DB settlement survive interruption, competing upstream writes, changed landing identities, and gateway restore without dual-authority ambiguity.

**Native authority:** separately approved after the retained migration program. This document does not assert it is reached.

### 26.2 Final architectural decision

**One immutable substrate and transaction framework; separate domain models and solver families; SDN-only native control surfaces; independent validation; one explicit acceptance authority per protected scope.**

Tree-sitter tells SCV where source structure is. A source solver reasons about entities and edits. A database solver reasons about stable columns, rows, schema versions, and constraints. The gateway settles aliases and publishes accepted results. Shared hashing, compression, capture, scheduling, and evidence make those capabilities efficient without pretending their conflict semantics are identical.

---

## 27. Research and source references

### 27.1 Evidence boundaries

The earlier master plan was read in full and its requirements were consolidated. Current Simple source was inspected at the pinned revision below through the connected repository. External primary sources were consulted for parser behavior, merge mechanisms, identity/schema precedents, hashing, gateway primitives, and selective retrieval.

Source existence is not execution evidence. No native SDN example, Simple test, conflict benchmark, hash-conformance suite, or network gateway was executed for this document. Upstream behavior is cited as a mechanism to study, not as proof that SCV already implements it. New schema keys, APIs, commands, paths, thresholds, tasks, and scenarios remain proposals until accepted.

### 27.2 Primary research and implementation references

| Ref | Source | Specific use / limit |
|---|---|---|
| R01 | [Anthropic: Redesigning Source Control][R01] | Scion changed-file records, derived data, immutable caches, server operations and separate ref acceptance. Do not inherit its mandatory-online client policy. |
| R02 | [Tree-sitter: Advanced Parsing][R02] | Incremental edits/reparse, included ranges, and tree ownership; not a merge-policy engine. |
| R03 | [Mergiraf architecture][R03] and [commutative merging profiles][R03b] | Structured reconstruction and explicitly scoped commutativity; not a universal reorder permission. |
| R04 | [Apache Iceberg: Evolution][R04] | Stable column IDs as a precedent for safe rename/reorder/drop behavior; no Iceberg runtime dependency is proposed. |
| R05 | [Automerge: Conflicts][R05] | Convergence and retained alternative values; SCV must keep unresolved business conflicts visible rather than hide them behind a display winner. |
| R06 | [SQLite changeset conflict categories][R06] and [changeset application][R06b] | Different row/data/constraint/FK failures require different handling; SCV admission does not inherit permissive omission semantics. |
| R07 | [Jujutsu conflicts][R07] | Conflicts as repository data and later resolution. No assertion that jj inherently causes more conflicts. |
| R08 | [Git rerere][R08] | Reusing prior conflict resolutions; SCV adds domain/schema/provider/precondition binding and validation. |
| R09 | [Cyan4973/xxHash][R09] | Official portable C, XXH3 output semantics, optimized implementations and test vectors. |
| R10 | [BLAKE3-team/BLAKE3][R10] and [C API/build documentation][R10b] | Official C/Rust, secure hashing, streaming, SIMD and optional parallel execution. |
| R11 | [ogxd/gxhash][R11] | Optional accelerated noncryptographic fingerprinting; preserve version/hardware/capability distinctions. |
| R12 | [Git fast-import][R12] | Gateway object conversion without mandatory full checkout; not native SCV storage. |
| R13 | [Git update-ref][R13] | Expected-old-value updates and ref transaction mechanics; backend-specific contracts still need actual tests. |
| R14 | [Repoformer, ICML 2024][R14] | Selective repository-completion retrieval evaluation; SCV task results must be measured separately. |
| R15 | [Repoformer upstream repository][R15] | Retained code/evaluation entry point from the prior plan; pin and reproduce before making implementation claims. |
| R16 | [HyperAST implementation][R16] and [ASE 2022 research page][R16b] | Retained prior-plan reference for shared syntax DAGs/history analysis; not a complete durable repository store. |
| R17 | [GumTree][R17] | Retained structural edit/move-matching reference; use bounded, ambiguity-preserving integration. |
| R18 | [Sapling/Mononoke][R18] | Retained server-side derived data, VCS-neutral modeling and large-repository architecture reference. |

R15–R18 retain prior research directions rather than asserting a new source-level upstream implementation audit in this document. All deployable upstream code, vectors, grammars, and models must be pinned by reviewed artifact/version digests before implementation acceptance.

### 27.3 Pinned Simple source

All code links in this table use `684af83fa9818aa5bfde83e065372bf204c9e651`.

| Ref | Inspected source | Evidence scope |
|---|---|---|
| S00 | [Audit revision][S00] | Repository anchor returned by the connected GitHub source. |
| S01 | [Rust SDN public module/documentation][S01] | Actual nested/map/array/table syntax and flat-only `parse_config` distinction. |
| S02 | [Strict SDN value/limit types][S02] | Bounded syntax representation; no implicit schema or trust admission. |
| S03 | [Distributed identity][S03] | Existing actor-incarnation/counter UID and epoch/sequence alias model. |
| S04 | [DB typed patch model][S04] | Name-based field addressing, current operation types, and legacy SHA-256 v1 restrictions in inspected code. |
| S05 | [DB reducer][S05] | Existing pure preview and field-specific merge rules. |
| S06 | [DB constraints/set primitives][S06] | Observed-remove behavior and constraint values. |
| S07 | [DB allocation][S07] | Existing authenticated candidate planning and settled-reference projection. |
| S08 | [Editor IPC][S08] | Actual spool transport and documented native transport TODO at the audit revision. |
| S09 | [Source merge validation][S09] | Current narrow byte/parse checks and caller-supplied compile/test statuses; not universal or complete validators. |
| S10 | [Network remote][S10] | Documented filesystem/loopback simulation and future HTTPS integration. |
| S11 | [Shared BLAKE3][S11] | Current arbitrary-length implementation description, superseding the old short-input finding; conformance not executed here. |

### 27.4 Previous plan and status reconciliation

The conversation's `scv_master_implementation_plan_2026-10-16.md` is the prior 26-section, 61-task design. This document retains its storage/hash/recovery/evaluation guarantees, replaces its tentative SDN-style control example with an explicit SDN-only contract, adds domain solver plugins and full textual-DB concurrency, and incorporates the subsequent gateway/operation-capture discussion.

Do not copy an old defect into the tracker without verifying the current revision. Specifically, the old common-BLAKE3 64-byte limit is no longer the current source description. Conversely, source comments describing broad support are not proof of conformance. Record the current tested status independently.

[R01]: https://www.anthropic.com/engineering/redesigning-source-control
[R02]: https://tree-sitter.github.io/tree-sitter/using-parsers/3-advanced-parsing.html
[R03]: https://mergiraf.org/architecture.html
[R03b]: https://mergiraf.org/adding-a-language/enabling-commutative-merging.html
[R04]: https://iceberg.apache.org/docs/latest/evolution/
[R05]: https://automerge.org/docs/reference/documents/conflicts/
[R06]: https://www.sqlite.org/session/c_changeset_conflict.html
[R06b]: https://www.sqlite.org/session/sqlite3changeset_apply.html
[R07]: https://docs.jj-vcs.dev/latest/conflicts/
[R08]: https://git-scm.com/docs/git-rerere
[R09]: https://github.com/Cyan4973/xxHash
[R10]: https://github.com/BLAKE3-team/BLAKE3
[R10b]: https://github.com/BLAKE3-team/BLAKE3/blob/master/c/README.md
[R11]: https://github.com/ogxd/gxhash
[R12]: https://git-scm.com/docs/git-fast-import
[R13]: https://git-scm.com/docs/git-update-ref
[R14]: https://proceedings.mlr.press/v235/wu24a.html
[R15]: https://github.com/amazon-science/Repoformer
[R16]: https://github.com/HyperAST/HyperAST
[R16b]: https://conf.researchr.org/details/ase-2022/ase-2022-research-papers/110/HyperAST-Enabling-Efficient-Analysis-of-Software-Histories-at-Scale
[R17]: https://github.com/GumTreeDiff/gumtree
[R18]: https://github.com/facebook/sapling/tree/main/eden/mononoke
[S00]: https://github.com/ormastes/simple/commit/684af83fa9818aa5bfde83e065372bf204c9e651
[S01]: https://github.com/ormastes/simple/blob/684af83fa9818aa5bfde83e065372bf204c9e651/src/compiler_rust/sdn/src/lib.rs
[S02]: https://github.com/ormastes/simple/blob/684af83fa9818aa5bfde83e065372bf204c9e651/src/lib/common/sdn/strict_types_v1.spl
[S03]: https://github.com/ormastes/simple/blob/684af83fa9818aa5bfde83e065372bf204c9e651/src/lib/scv/distributed_identity.spl
[S04]: https://github.com/ormastes/simple/blob/684af83fa9818aa5bfde83e065372bf204c9e651/src/lib/scv/db_patch.spl
[S05]: https://github.com/ormastes/simple/blob/684af83fa9818aa5bfde83e065372bf204c9e651/src/lib/scv/db_reducer.spl
[S06]: https://github.com/ormastes/simple/blob/684af83fa9818aa5bfde83e065372bf204c9e651/src/lib/scv/db_schema.spl
[S07]: https://github.com/ormastes/simple/blob/684af83fa9818aa5bfde83e065372bf204c9e651/src/lib/scv/db_allocation.spl
[S08]: https://github.com/ormastes/simple/blob/684af83fa9818aa5bfde83e065372bf204c9e651/src/lib/scv/editor_ipc.spl
[S09]: https://github.com/ormastes/simple/blob/684af83fa9818aa5bfde83e065372bf204c9e651/src/lib/scv/merge_validation.spl
[S10]: https://github.com/ormastes/simple/blob/684af83fa9818aa5bfde83e065372bf204c9e651/src/lib/scv/network_remote.spl
[S11]: https://github.com/ormastes/simple/blob/684af83fa9818aa5bfde83e065372bf204c9e651/src/lib/common/crypto/blake3.spl

---

**End of plan.** All new implementation tasks and acceptance scenarios remain proposed until their linked execution evidence is recorded.
