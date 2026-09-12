# EGL wave receipts — 2026-09-12

`doc/03_plan/agent_tasks/environment_optimized_dynamic_libraries.md` is inside
the Codex ownership fence for this wave, so no agent wrote into it and the
integration branch `work/egl-wave-2026-09-12` does not touch it. Every receipt
paragraph the wave produced is collected here verbatim, each under a pointer
naming the section of that plan document it is destined for. The plan's owner
can move them without re-deriving anything.

Branch: `work/egl-wave-2026-09-12`, base `bd8df49e8d4` (EGL core base).
Binary identity for every measurement below unless a paragraph says otherwise:
`/home/yoon/dev/simple/bin/release/aarch64-unknown-linux-gnu/simple`,
50,093,192 bytes, 2026-09-06 09:59:11 +0900 (Rust bootstrap seed; no
pure-Simple full-CLI binary is deployed on this host).

## Contents — destination pointer per section

- Agent P → `## Lexical summary follow-up (2026-09-08)` and `## AVX2 lexical primitive follow-up (2026-09-08)`
- Agent W → new `### Package 5 receipt (2026-09-12)`, before `## Lexical summary follow-up (2026-09-08)`
- Agent V → new `### Package 4 receipt (2026-09-12)`, immediately before `### Package 8 owner handoff`
- Agent U → new `## Package 2 receipt (2026-09-12)`, appended at end of document
- Agent X → new `### Package 7 receipt (2026-09-12)`, between the "Current package status" table and `### Package 8 owner handoff`
- Agent T → `## Packed GPU completion follow-up (2026-09-08)` and `## Backend callback bridge follow-up (2026-09-08)`
- Agent N → `### Package 8 owner handoff` (pointer only; the receipt itself is `doc/08_tracking/todo/egl_package8_host_capability_ledger_2026-09-12.md`)
- Agent Q → `## Parser variant build-plan follow-up (2026-09-08)` — **PENDING, not integrated** (see below)
- Agent K → no plan-document section; CI wiring, receipt is its commit message

---

## Agent P → `## Lexical summary follow-up (2026-09-08)` + `## AVX2 lexical primitive follow-up (2026-09-08)`

Receipt 2026-09-12 (scalar owner, boundary-state qualification). The canonical
scalar module `src/lib/nogc_async_mut/structural/parse/lexical_block_summary_v1.spl`
and its sibling `lexical_transition_table_v1.spl` existed only as uncommitted
2026-09-08 files in the shared working copy; they were brought into a clean
worktree unchanged before any edit. A new red-first spec,
`test/01_unit/lib/structural_parse_lexical_block_summary_boundary_states_v1_spec.spl`,
qualifies the summary across boundary states that a chunked caller can produce:
empty-block identity, no-evasion through an interposed empty block, validity of
every reachable output state, over-wide and unreachable-input refusal, and
mismatched-boundary composition refusal. It ran red (3 passed, 2 failed) on
`bin/release/aarch64-unknown-linux-gnu/simple` (50093192 bytes, 2026-09-06
09:59:11 +0900): `lexical_block_summary_scalar_v1` retired the pending
quote-run, raw-prefix, identifier, slash, and post-newline facts
unconditionally, so a zero-length block erased them and a split introducer
(`r` | `` | `"`) evaded its fallback tag. The fix guards that retirement with
`if bytes.len() > 0`, making an empty block the identity. Green 5 of 5, with
`structural_parse_lexical_block_summary_v1_spec.spl` (6 of 6),
`structural_parse_lexical_transition_table_v1_spec.spl` (6 of 6) and
`test/01_unit/lib/structural/parse/parse_cpu_reference_spec.spl` (18 of 18)
unchanged.

Receipt 2026-09-12 (SIMD owner, contract only). The independent-block lowering
of the same masks/state contract is `lexical_transition_table_v1.spl`, whose
spec already pins the selected initial row against the sequential scalar scan
for every 33-byte partition; that equivalence still holds after the empty-block
fix, so no second table was added. AVX2 execution proof is not produced here:
the host is aarch64 (`uname -m` = aarch64, `grep -c avx2 /proc/cpuinfo` = 0), so
the qualification is source-only mask/state equivalence against the scalar
oracle, not executed SIMD evidence.

Receipt 2026-09-12 (frontend owner, no change). The consume-untagged /
route-tagged line is already owned by
`src/compiler/99.loader/frontend_lexical_advisory_adapter_v1.spl`, which reads
`summary.fallback_bits` and `summary.canonical_usable` and holds
`reference_frontend_required`. That file is inside another session's ownership
fence, so nothing was added beside the summary module to avoid a second router.

Receipt 2026-09-12 (next SIMD lane, blocked). The authenticated provider-owned
batch was not built here because it already exists inside another session's
ownership fence: `src/compiler/99.loader/parser_structural_mask_batch_v2.spl`
and `parser_structural_package_owner_v1.spl`, with the exact-ABI seam
`parser_lexical_mask_call_native_v1.spl` committed on
`codex/gl-production-current-main-sol-20260912`. Writing a scalar-provider batch
in a second worktree would duplicate that seam rather than invoke it, so the
lane stays blocked on those files landing. What was done instead: the primitive
module `src/compiler/70.backend/backend/native/parser_lexical_avx2_classifier_v1.spl`
and its 2026-09-08 contract spec
`test/01_unit/compiler/backend/parser_lexical_avx2_classifier_v1_spec.spl` were
brought into a clean worktree unchanged and executed on
`bin/release/aarch64-unknown-linux-gnu/simple` (50093192 bytes, 2026-09-06
09:59:11 +0900): 4 of 4 green, covering interface/size declaration, the exact
SysV callable bytes, exact masks including high bytes without input mutation,
and tail rejection. Those bytes are emitted, not executed; this host is aarch64
and produces no AVX2 execution evidence.


---

## Agent W → new `### Package 5 receipt (2026-09-12)`

### Package 5 receipt (2026-09-12)

Added the candidate-classification, routing-verification, and advisory-wrapper
legs on top of the sealed 22-state transition table, in pure Simple, red first.

- `src/lib/nogc_async_mut/structural/parse/lexical_candidate_resolution_v1.spl`
  (165 lines): the nine published candidate classes as per-byte class bits and
  as block masks derived two independent ways — per-needle byte equality,
  mirroring the native one-needle primitive, and a fold of the per-byte class
  bitset — plus scalar state resolution through the sealed table and through
  unsealed rows. The batch forms seal/validate once per block and return every
  admitted-state result in table order.
- `src/lib/nogc_async_mut/structural/parse/lexical_routing_receipt_v1.spl`
  (91 lines): `LexicalRoutingReceiptV1` plus issue/verify. Verification trusts
  no receipt field — masks and resolved state are recomputed from the claimed
  bytes and input state — so a forged mask, forged output state, forged byte
  count, forged `scalar_resolution=false`, stale generation, wrong input state,
  and a native-provider claim the host never admitted are each refused with a
  distinct reason; a truthful receipt verifies, for every admitted state.
- `src/lib/nogc_async_mut/structural/parse/lexical_advisory_wrapper_v1.spl`
  (79 lines): `lexical_advisory_scan_v1` always returns the scalar summary and
  the scalar-resolved state. An admitted provider supplies candidate masks
  only; disagreement is reported as per-class divergence bits (with a separate
  width-divergence reason, so a wrong block width is never misattributed to a
  mask), and a diverged provider yields a `ScalarReference` receipt — it
  contributed nothing, so the receipt records the fallback rather than a
  provider that was merely offered.

Specs, all new and all RED before the modules existed (`outcome=ERROR
executed=0`, "does not export 'lexical_candidate_resolution_v1'"), now
6/6 + 6/6 + 6/6 = 18 examples:
`test/01_unit/lib/structural_parse_lexical_candidate_resolution_v1_spec.spl`,
`..._lexical_routing_receipt_v1_spec.spl`, `..._lexical_advisory_wrapper_v1_spec.spl`.
The exhaustive leg covers all 256 byte values against every one of the 22
admitted states (5,632 compared resolutions, 0 mismatches, both the compared
count and the identity-selection cross-check count asserted so it cannot pass
vacuously). The pre-existing `structural_parse_lexical_transition_table_v1_spec.spl`
and `structural_parse_lexical_block_summary_v1_spec.spl` are 6/6 before and
after. Deployed seed `bin/release/aarch64-unknown-linux-gnu/simple`,
50,093,192 bytes, 2026-09-06 09:59:11 +0900; no Rust and no C changed.

Perf finding recorded rather than fixed, because it is in the transition-table
owner's module: `_state_id_ltt` rebuilds the whole 22-state admitted list on
every call, so one identity-selection costs ~9.7 ms in the interpreter and a
naive 256x22 exhaustive run took over 900 s (the runner's default child timeout
is 120 s, `test_runner_single.spl:218`). Batch resolution plus a sampled
identity cross-check brings the spec to 64 s; a memoized state index in
`lexical_transition_table_v1.spl` would remove the term entirely.

Not done, with the blocker: native x86/self-host qualification and emitted
v3/v4 siblings need an x86_64 host — this one is `aarch64` with no AVX2
(`uname -m` = aarch64, no avx2 flag in `/proc/cpuinfo`), so no AVX2 artifact
can be emitted, mapped, or executed here and no provider is admitted; every
native-provider path above is exercised only through a fake offered mask set.
Broader lexical coverage stays with the lexical-summary owner.


---

## Agent V → new `### Package 4 receipt (2026-09-12)`, immediately before `### Package 8 owner handoff`

### Package 4 receipt (2026-09-12)

Landed the stable parse-result provider seam and its normalized scalar dialect
parity as a sibling module, not as frontend wiring:
`src/compiler/80.driver/parse_result_provider_seam_v1.spl` (412 lines) with
`test/01_unit/compiler/driver/parse_result_provider_seam_v1_spec.spl` (249
lines) over the frozen corpus `test/fixtures/parse_result_provider_seam_v1/`
(five sources: functions, type declarations, interpolation, trait/impl/const,
and one that must produce a parser diagnostic). No existing source, test, or
fixture file was modified.

`ParseResultProviderV1` is a struct of callables — no inheritance, no registry
object — carrying `provider_id`, `implementation_identity`, `generation`,
`available`, `unavailable_reason`, and a
`fn(ParseRequestV1) -> Result<ParseNormalizedResultV1, ParseResultRefusalV1>`.
Struct-held callables and `Result`-returning callable fields were probed on the
deployed seed before the design was chosen, rather than assumed.
`parse_result_seam_request_v1` validates schema, availability, dialect, and
source identity before dispatch, so the refusals (`ProviderSchemaMismatch`,
`ProviderUnavailable`, `UnsupportedDialect`, `InvalidRequest`) are typed rather
than a nil result. The scalar provider is the existing entry
`parse_and_build_module_scoped`; the SIMD/variant slot is a real provider value
whose callable refuses unconditionally, with the receipt "no admitted SIMD parse
provider: build host is aarch64 (Cortex-X925, no AVX2) and no parser variant
artifact has been mapped; see package 5" — nothing is mapped and nothing is
executed. The host CPU claim is from `lscpu` on this machine.

Normalization produces `ParserScalarNormalizedOutputV1` (reused from
`parser_scalar_parity_v1.spl`, which is read here and not rewritten) from
length-prefixed, ordered material, following the frontend-seam todo's resume
step 4: the token digest walks the same lexer the parser uses and records kind,
line, column and text per token plus a trailing count; the span digest walks
`function_order` and records each declaration's start/end/line/col/length/file;
the node digest records the module name, layer tags, collection counts, per
function parameter/type-parameter/attribute counts and the seven declaration
flags, then sorted key sets for the Dict-held declarations; the diagnostic
digest covers `parser_get_errors()`, drained immediately after the parse because
the next `parser_init_with_path` resets that channel. No 32-bit lexical hash is
used as identity.

Red→green on the deployed seed `bin/release/aarch64-unknown-linux-gnu/simple`
(50093192 bytes, 2026-09-06 09:59:11): RED
`outcome=ERROR declared>=8 executed=0 passed=0 failed=0`, run result
`1 total, 0 passed, 1 failed`, cause
`error: runtime: Module "compiler.driver" does not export 'parse_result_provider_seam_v1'`;
GREEN `outcome=OK declared>=8 executed=8 passed=8 failed=0`, 33.1s, and
`8 total, 8 passed, 0 failed` again after the final cleanup pass. The parity
assertions were checked for vacuity by a controlled seam-only mutation
(normalizing the seam leg under `path + "#seam"`): 8 executed, 6 passed, 2
failed — `matches the direct parser entry after normalization` and
`qualifies seam-versus-direct parity through the parity owner` — then reverted.

Neighbouring specs, same seed, controlled A/B with the three new paths moved
aside and restored: `test/05_perf/frontend_interpolation_scaling_spec.spl`
2/2 PASS with the change (ratio 4222377/2691320 = 1.57) and 2/2 PASS without it
(6160272/3411833 = 1.81). An intermediate run of that spec failed at ratio 3.41
while a `bin/simple lint` shared the host; it passes on a quiet host with and
without the change, so that failure is host load, not a regression — read the
ratio, as that spec's own header says. Four representative specs from
`test/01_unit/compiler/frontend/` were run on both sides and are byte-identical
across the A/B: `collection_desugar_gate_spec.spl` 4/4 PASS, while
`ast_types_spec.spl` (0/1), `bootstrap_expr_stmt_arena_spec.spl` (4/14) and
`annotation_registry_empty_reset_source_spec.spl` (0/1) fail identically at base
`bd8df49e8d4` with the new files absent. Those three are pre-existing failures
in this lane's base, untouched by this change; the other 113 files in that
directory were not run. `bin/simple lint` on the new module exits 0 with
uncertain `unnamed_duplicate_typed_args` suggestions only.

What remains, with its blocker. The seam is not called by
`parse_full_frontend_with_scope`: `src/compiler/10.frontend/frontend.spl` and
the rest of the parser-framework neighborhood are owned by the concurrent Codex
lanes listed in
`doc/08_tracking/todo/environment_optimized_dynamic_libraries_frontend_seam_2026-09-07.md`,
whose unblock condition is ownership transfer, so no consumer was rewired and
this is source-only wiring evidence for the port itself. The dialect
grammar/actions/schema/semantic-profile identities are declared labels derived
from the dialect id, not digests computed from grammar tables, action tables or
schema files; computing real ones is frontend-seam work. Only the Simple dialect
is admitted — SDN and sosh keep separate result models and would each need a
normalization adapter. Parity here is seam-versus-direct-parser on one host,
which is not legacy-versus-canonical promotion evidence, and
`parser_scalar_parity_qualify_v1` is fed two distinct implementation identities
precisely because it refuses a self-comparison.

### Package 4 follow-up receipt (2026-09-12, computed dialect identity)

The dialect grammar/actions/schema/semantic-profile identities are no longer
declared labels. `src/compiler/80.driver/parse_dialect_identity_v1.spl` (178
lines) computes them from the tables a provider executes: the grammar component
is the kind ↔ name round trip over the whole kind domain of
`src/compiler/10.frontend/core/tokens.spl` (`kind_limit = 222`, `TOK_KW_AS = 221`
being the highest constant there), the actions component is `tok_precedence` /
`tok_is_right_assoc` / `token_requires_rhs` / `token_can_end_expr` packed per
kind, and schema and semantic come from the dialect projection's
token+span and node+diagnostic digests for a fixed probe source. The probe domain
is derived from the tables themselves, not from a name list restated in the
module. `src/lib/*/structural/parse` was deliberately not digested: those tables
are the SIMD/variant twin's, not what `parse_and_build_module_scoped` runs.
`ParseResultProviderV1` gains `tables` and the dialect identity it CLAIMS; the
seam recomputes the identity from the tables, refuses `ProviderSchemaMismatch`
when the claim does not follow, refuses `UnsupportedDialect` against
`provider.tables.dialect_id`, and stamps the verified identity onto the admitted
result. Verification re-enters no GLOBAL-STATE parser: the Simple probe output is
computed once per tables value, never during a request, so an in-flight parse's
error channel is never reset under it. SDN's own lexer and parser are stateless
`Result`-returners and are re-run during verification.

`src/compiler/80.driver/parse_dialect_adapters_v1.spl` (273 lines) adds the SDN
dialect (id 2) as a second scalar provider through the same seam, projecting the
minimal stable fields the design document leaves unspecified — the real
`tokenize` walk, the parser's own dotted-path span table with sorted keys, the
canonical encoding `sdn_encode_canonical` already produces as the node digest,
and `parse_with_issues` diagnostics. Spec
`test/01_unit/compiler/driver/parse_dialect_identity_and_adapters_v1_spec.spl`
(253 lines, 11 examples, fixtures `test/fixtures/parse_dialect_adapters_v1/*.sdn`)
went RED `outcome=ERROR declared>=11 executed=0`, cause
`Module "compiler.driver" does not export 'parse_dialect_identity_v1'`, to GREEN
`outcome=OK executed=11 passed=11 failed=0` (45511ms) on the deployed seed
`bin/release/aarch64-unknown-linux-gnu/simple` (50093192 bytes, 2026-09-06
09:59:11). Agent V's own spec is unedited and still 8/8. Non-vacuity is asserted:
a fixture whose `classify` diverges on one keyword must move the grammar digest
AND leave the other three components equal, and the same tables on the real
scalar provider must be refused `ProviderSchemaMismatch`.

`frontend.spl` is still not rewired — it remains owned by a concurrent lane — but
the compatibility example now calls its public entry `parse_full_frontend` and
requires the seam result to be byte-identical after normalization, so the
one-line hook is a behaviour-preserving edit rather than an assertion about one.

Two things remain, both recorded rather than implied. The sosh dialect adapter
could not be written: `os.apps.shell.shell_script.StmtKind` is shadowed by
`src/compiler/10.frontend/parser_types_expr.spl`'s `StmtKind` under
co-compilation, so importing the seam and `ScriptEngine` into one spec breaks
`ScriptEngine.parse` outright — six-line reproduction, the measured fact that an
aliased import does not help, and the fix in
`doc/08_tracking/bug/shell_stmtkind_collides_with_frontend_stmtkind_2026-09-12.md`.
And per-request identity verification is expensive on this seed: agent V's spec
went 17860ms to 67238ms for the same 8 examples (~25 requests, ≈2s each), so the
frontend hook should not be applied until an admit-once entry hoists verification
off the request path — deliberately not a cache keyed on provider id or
generation, since the mutated fixture carries the real provider's both.

---

## Agent U → new `## Package 2 receipt (2026-09-12)`, appended at end of document


## Package 2 receipt (2026-09-12)

Package 2's remaining owner work was "real callable mapping and native/SMF
parity". The mapping half is delivered and executed on this host; the parity
half is delivered as native-vs-static, with SMF wired and refusing rather than
claimed.

What landed, pure Simple:

- `src/lib/nogc_sync_mut/composition/environment_variants/callable_map_v1.spl`
  (327 lines) — the loader owner every upstream module deferred to and none
  implemented. `receipt_v1` states it "does not load a library, invoke a symbol,
  or inspect the host"; `binding_runtime_v1` states its provider handles "are
  scalar identities supplied by the loader owner" and that it "never maps or
  invokes an artifact". This module maps an admitted variant's exported symbol
  identity onto a genuinely resolvable callable for the exact `i64(i64, i64)`
  operation family, uniformly across placements, and refuses with ten stable
  codes rather than returning a nil placeholder. Artifact bytes are hashed and
  compared BEFORE the artifact is mapped, per the architecture's requirement
  that native metadata checks precede `dlopen` because constructors run during
  load. `mapping_handle` / `callable_handle` are opaque derived tokens; the raw
  address stays in a file-private field, per the design's "never native
  addresses in the public contract". Package-1 admission is consumed, not
  re-derived: the request carries `admitted_abi_digest` / `admitted_generation`
  and disagreement is refused.
- `src/lib/nogc_sync_mut/sffi/dynlib_exact_admission_v1.spl` (93 lines) — the
  runtime boundary, placed under the already-allowlisted `sffi/` provider
  directory so the ratchet scope is unchanged. It exists because two measured
  defects on the deployed seed (aarch64, 2026-09-06) made the existing surface
  unusable for a fail-closed loader: `ExactArtifactDynLib.load_exact_linux`
  calls `spl_dynlib_snapshot_linux`, which this seed answers `semantic: unknown
  extern function`; and `spl_dlsym` on a missing symbol RAISES
  `runtime: spl_dlsym: unresolved symbol` and kills the process, as do
  `sym_checked`, `resolve_i64_checked` and `VersionedDynLib.has_symbol`, because
  the `*mut i64` writeback they depend on is lost on seeds built before
  2026-09-11. The `rt_host_dynlib_*` family answers a miss with 0 and does not
  raise, so a missing symbol can be refused instead of being fatal. Execution
  rides the direct-return `spl_wffi_call_i64`: the checked transport was
  measured answering `Ok(0)` for a call that really produced 222, which is the
  silent-wrong-result class NFR-001 forbids.

Spec: `test/01_unit/lib/nogc_sync_mut/composition/environment_variants/callable_map_v1_spec.spl`
(349 lines). Red first — `outcome=ERROR declared>=4 executed=0 passed=0
failed=0`, `Module "std.nogc_sync_mut.composition.environment_variants" does not
export 'callable_map_v1'`. Green after — `outcome=OK declared>=4 executed=4
passed=4 failed=0`.

The parity example builds a three-line C shared object with `cc -shared -fPIC`
on this host, admits it against its own SHA-256, resolves `egl_pkg2_mix2`, and
runs it through `spl_wffi_call_i64` against a static in-process twin of the same
operation: `native=[222, 0, -82, 31000110] static=[222, 0, -82, 31000110]`. Both
placements are then driven through the real `receipt_v1` state machine
(discover → metadata → self-check → eligible → mapped → callable → bound →
active → executed, with mapped/callable supplied by the new owner) and asserted
to produce an identical lifecycle PROJECTION — state sequence, execution digest,
execution count, event sequence, provider generation — plus identical ABI
digest, arity and operation id on the callable itself. The receipt structs are
compared through that projection, not field by field. The mask is exactly
`artifact_digest`, `mapping_handle`, `callable_handle` and
`state_evidence_digest` — the four values that describe WHERE the operation
lives, the last because `mark_mapped`/`mark_callable` fold the artifact digest
into the evidence chain — and the spec asserts the artifact digests DIFFER
rather than letting them silently coincide.
Non-vacuity was verified directly: changing the C fixture's `a*31+b` to `a*32+b`
makes the example fail with `native=[229, 0, -85, 32000113] static=[222, 0, -82,
31000110]`.

Refusals are asserted as hard as success: absent symbol (native and static),
artifact-digest mismatch, absent artifact, ABI mismatch, stale provider
generation, unsupported arity, and the two placement refusals below.

What remains, with its exact blocker:

- **SMF is not executed, and this receipt does not claim it is.** The lane is
  wired and refuses with its own code
  (`VARIANT_CALLABLE_PLACEMENT_UNAVAILABLE_V1`), kept distinct from
  `VARIANT_CALLABLE_PLACEMENT_UNSUPPORTED_V1` so a receipt can tell "real
  placement, unavailable on this base" from "out of scope". The blocker is that
  no in-process SMF invoke path exists at this base: `smf_dlsym`
  (`src/os/smf/smf_dynlib.spl`) returns a section OFFSET, not a callable
  address; `exec_mapping_map_rx` (`src/compiler/99.loader/loader/exec_mapping.spl`)
  maps bytes with no entry ABI; `validated_smf_load` returns a mapping, not a
  callable; and `src/os/smf/smf_dynlib.spl` is owned by the
  `codex/egl-prod-integration` lane and off limits to this one. The parity
  harness is placement-generic, so the SMF lane needs only a mapping function
  once that owner publishes an entry ABI.
- **Artifact identity is not fd-pinned.** The digest is taken by path and the
  artifact is then opened by the same path, so a swap between the two calls is
  undetected, and the architecture's "identities bind to the exact bytes mapped"
  is not met yet. The snapshot-descriptor route that closes it
  (`ExactArtifactDynLib.load_exact_linux`: hash `/proc/self/fd/N`, dlopen that
  descriptor) is unavailable because `spl_dynlib_snapshot_linux` is an unbacked
  extern on this seed — it answers `semantic: unknown extern function`.
- The mapped operation family is exactly `i64(i64, i64)`. Widening it means
  widening the foreign call bridge; the bound is stated in
  `VARIANT_CALLABLE_SUPPORTED_ARITY_V1` rather than assumed.
- No production consumer is wired yet: the callable owner is exercised by its
  spec, not by a startup or CLI path.

Binary identity for every run above:
`/home/yoon/dev/simple/bin/release/aarch64-unknown-linux-gnu/simple`,
50093192 bytes, 2026-09-06 09:59:11 (the deployed seed; no rebuild was needed —
this change is `src/lib` only, which is read as source every run). Host probed:
aarch64 Cortex-X925/A725, no AVX2, `clang` at `/home/yoon/dev/llvm/install/bin/clang`,
`readelf`/`objdump`/`llvm-readobj` present.

Regression re-runs on that binary, before and after, byte-identical verdicts:
`provider_generation_spec` 3/3, `environment_variant_policy_strict_v1_spec` 5/5,
`environment_variant_composite_selector_strict_v1_spec` 3/3,
`x86_variant_admission_v1_spec` 12/12. Two pre-existing reds were confirmed on
the clean base commit `bd8df49e8d4` and are NOT caused by this change:
`feature_registry_v1_spec` 4/5 ("keeps VBMI and VBMI2 outside plain x86-64-v4")
and `wffi_into_bytes_spec` 0/5. `sh scripts/check/check-no-direct-rt.shs --roots src`
reports the same `FAIL — forbidden direct rt_* count 6343 exceeds baseline 6072`
on the clean base and after this change: the new `rt_*` sites are inside the
allowlisted `sffi/` provider directory, so the forbidden count is unchanged.

---

## Agent X → new `### Package 7 receipt (2026-09-12)`, between the "Current package status" table and `### Package 8 owner handoff`

### Package 7 receipt (2026-09-12)

Resident frontend/render execution and transfer-aware scheduling are implemented
in pure Simple, red-first, and green on this host. Package 7's prior evidence was
architecture plus the routing-only queue seam (`engine2d_gpu_epoch_admit`,
`common.gpu.engine2d.gpu_epoch`), which re-decides admission on every call and
keeps nothing alive between calls.

What landed:

- `src/lib/gc_async_mut/gpu/engine2d/environment_resident_executor_v1.spl` (241 lines) —
  `ResidentExecutionIslandV1`, an admit -> resident -> retire island. `admit`
  grants one lease after `gpu_bounded_task_validate_v1` accepts the package-6
  bounded task, and refuses when the provider authority is absent and
  `gpu_task_missing_provider_decision_v1` does not return `UseCpu`
  (`AuthorityMissing`); `execute` renders onto the already-admitted surface with
  no re-admission; `sweep` retires leases past the island's idle bound and
  leaves the record so a stale lease answers `NotResident`; `retire` returns the
  terminal receipt and frees the slot. Both package-6 authorities are consumed,
  not re-derived. Receipts carry `lane`, `device_execution_proven`,
  `routing_evidence_only`, execution count, residency ticks and the readback
  checksum.
- `src/lib/common/gpu/environment_transfer_scheduler_v1.spl` (224 lines) —
  `transfer_aware_plan_v1`, one deterministic plan over declared host/device
  transfer costs under a byte budget. Tasks sharing a `residency_class` are
  batched and their upload is charged once; ordering is starved-first, then
  cheapest crossing, then class identity, so arrival order does not affect the
  plan; a class deferred `TRANSFER_SCHEDULER_STARVATION_BOUND_V1` times is
  admitted even when it does not fit and is named in `forced` with
  `budget_exceeded_by_forced`, so the plan never hides having exceeded its
  budget. `plan_identity` names the plan.

Specs (red first — both files failed with the module missing, 0 examples passed):

- `test/01_unit/lib/gpu/engine2d/environment_resident_executor_v1_spec.spl`
  (210 lines) — 11 examples, 11 passed. Includes the joined case: a transfer
  plan decides the order, the island executes only what the plan admitted, and
  the over-budget task never runs.
- `test/01_unit/lib/common/gpu/environment_transfer_scheduler_v1_spec.spl`
  (135 lines) — 8 examples, 8 passed.

Binary identity: `/home/yoon/dev/simple/bin/release/aarch64-unknown-linux-gnu/simple`,
50093192 bytes, 2026-09-06 09:59:11 (Rust bootstrap seed; it announces that on
every run).

Lint: `bin/simple lint` on each source file separately reports `Lint passed: all
files clean` for the scheduler after fixing its four findings (three
`unnamed_duplicate_typed_args` call sites made named, `_join_u64` rewritten from
a concat-in-loop to `[text].join(",")` for COLL006). The executor keeps four
`primitive_api` warnings on bare `i64`/`i32` tick and pixel-dimension
parameters; the package-6 sibling
`src/lib/common/gpu/environment_variant_task_contract_v1.spl` carries the same
warning class, so wrapping single scalars in newtypes here would depart from the
surrounding idiom rather than match it.

Host probe (aarch64): `vulkaninfo --summary` DOES enumerate a device — NVIDIA
GB10, integrated, driver 580.173.02, Vulkan 1.4.312 — and
`/dev/dri/{card0,card1,renderD128}` exist, though `card0` is permission-denied
to this user and the Mesa/Turnip ICDs fail to open `renderD128`. No spec was
skipped for lack of a device. No device execution was attempted either: the
deployed binary is the bootstrap seed and the device lane lives in package-6
modules outside this agent's scope. The execution body is the existing
CPU/software rasterizer (`SoftwareBackend`), reused unchanged — no new renderer
— and residency is witnessed by pixels accumulating across calls on the surface
admitted once, not by a counter. A green run of these specs is therefore not
evidence of device execution, and the executor refuses an offered provider
(`DeviceLaneUnavailable`) rather than letting the CPU lane impersonate one.

Regression sweep (13 existing device-free engine2d/GPU specs, before and after,
same seed binary): 12 verdict lines byte-identical across the two runs, and the
13th (`draw_ir_runtime_queue_spec.spl`) had its before-run verdict line split by
leaked output from the abandoned broad walk, with its readable tail
`passed=14 failed=0 skipped=0` matching the after run exactly. `skipped=0` on
every one of the 15 files in this set. 10 pass; 3 fail identically before AND
after and are pre-existing at the base commit `bd8df49e8d4`, untouched by this
change:

- `test/01_unit/lib/common/gpu/simpleos_host_gpu_draw_ir_spec.spl` — 1 of 17,
  "validates image resources without payload allocation with encoder rejection
  parity"; not device-related.
- `test/01_unit/lib/gpu/engine2d/backend_probe_strict_spec.spl` — 6 failures,
  all typed-probe diagnostics (ROCm, CUDA selectable when runtime and device are
  available, OpenCL session proof beyond ICD evidence, OptiX unsupported for
  raster, CPU SIMD capability gating). This is the device-probe class, and it is
  red on a host where `vulkaninfo` does enumerate a GB10 — worth a look by the
  GPU-authority owner, though it is pre-existing and outside package 7.
- `test/01_unit/lib/gpu/engine2d/backend_software_damage_spec.spl` — CPU
  software-rasterizer damage tracking.

Skip accounting, stated honestly: 0 skipped across the 15 files actually run.
The abandoned broad walk over `test/01_unit/lib/gpu/engine2d/` printed a partial
`Results: 127 total, 122 passed, 5 failed, 4 skipped` before it was killed, so
4 skipped examples exist in that directory outside this set; this agent did not
identify or run them. The one spec there carrying skip markers
(`ffi_out_param_via_return_value_detection_spec.spl`) was run explicitly and
reports `skipped=0` (3 of 4 fail, pre-existing, FFI out-param detection, not
device-gated), so it is not their source. The sweep is this bounded 13-file set
rather than the full 87-file directory walk because the wider walk runs native
MCDC coverage compiles per spec and did not clear its first spec in 10 minutes
at host load 49 — abandoned for cost, never because a device was missing.

What remains:

- A device execution body. Wiring one means consuming the backend fence and
  retirement authority (`Engine2dBackendCompletionPortOwnerV1`,
  `engine2d_environment_packed_completion_bridge_v1`) at the packed-completion
  join. Those modules and that join belong to the packed GPU completion
  follow-up owner; this agent consumes their records through the seam and edits
  neither.
- Deferral feedback. `TransferTaskV1.deferrals` is carried by the caller; no
  loop yet feeds `plan.deferred` back into the next round's count, so the
  starvation bound is proven for a supplied deferral count rather than over a
  live scheduling loop.
- Costs are declared per task, not measured. Measured transfer bytes need the
  device lane above.

---

## Agent T → `## Packed GPU completion follow-up (2026-09-08)` + `## Backend callback bridge follow-up (2026-09-08)`

## Append under "## Packed GPU completion follow-up (2026-09-08)"

- Queue-owner completion/retirement slice (2026-09-12): the packed queue now has
  an authority route, `engine2d_draw_ir_runtime_queue_complete_packed_with_authority`
  (`src/lib/nogc_async_mut/gpu/engine2d/draw_ir_runtime_queue.spl:372-401`), beside
  the unchanged routing-only compatibility route. Its admission rules and
  single-use redemption ledger are
  `src/lib/nogc_async_mut/gpu/engine2d/packed_completion_authority_v1.spl` (113
  lines). The queue forwards the authority's own `Engine2dGpuDeviceEvidence`
  verbatim into `engine2d_gpu_epoch_advance` and never constructs evidence:
  `engine2d_gpu_device_evidence_none()` does not appear on this path, so
  `device_execution_proven` flips exactly when the owner's evidence qualifies.
  The epoch advances queued -> submitted -> gpu_finished -> completed, which is
  what the existing `# TODO: [gpu][P2]` at
  `draw_ir_runtime_queue.spl:362` asked for; that TODO stays because the
  compatibility route it annotates is deliberately unchanged. Spec:
  `test/01_unit/lib/nogc_async_mut/gpu/engine2d/packed_completion_authority_v1_spec.spl`,
  9 examples, RED `executed=0 passed=0` (module absent) -> GREEN `executed=9
  passed=9 failed=0`. Binary: `bin/release/aarch64-unknown-linux-gnu/simple`,
  50093192 bytes, 2026-09-06 09:59:11 (Rust bootstrap seed; no pure-Simple
  full-CLI binary is deployed on this host). What remains: the authority record
  is still caller-constructible, so every record in the spec is a validator
  fixture; issuing one from a retained native fence is the Vulkan-owner line and
  is untouched here.

## Append under "## Backend callback bridge follow-up (2026-09-08)"

- Queue-owner consumption (2026-09-12): packed completion now consumes an
  owner-issued callback authority instead of re-deriving its facts, and refuses
  without one. `engine2d_packed_authority_refusal`
  (`packed_completion_authority_v1.spl:74-96`) refuses, in order: no authority at
  all; a handle with a zero `completion_handle`/`owner_identity` (not
  owner-issued); a receipt not in phase `queued`; a queued receipt with no ring
  token; presentation to a different runtime queue; an authority that does not
  correlate with the epoch on all seven of queue_handle, backend_handle,
  queue/operation/scene/surface/arena generation; and an authority already in the
  redemption ledger. `completion_handle`/`owner_identity` mirror the opaque pair
  `Engine2dBackendCompletionAuthorityV1` carries, so a projection from the backend
  completion port could keep its identity across this seam. That projection does
  NOT exist yet and is not field-for-field: `_Engine2dBackendCompletionRecordV1`
  holds `epoch`/`packed_digest`/`lease_generation`/`fence_identity`/`readback_digest`
  (digests), not this record's seven generation fields, and Codex's own
  `engine2d_environment_variant_completion_bridge_v1` takes `device_evidence` as a
  SEPARATE argument rather than carrying it on the authority. Defining the adapter
  `Engine2dBackendCompletionPortOwnerV1.completions[i]` -> `Engine2dPackedCompletionAuthorityV1`,
  and deciding where its `Engine2dGpuDeviceEvidence` comes from, is a merge-owner
  decision this lane deliberately did not make. Redemption is
  recorded only after validation passes, so a refusal does not burn a handle that
  was presented against the wrong epoch. Single-use is pinned in both directions
  by the spec's replay scenario, and the burned-handle branch (a validated
  authority presented against a host queue holding no packet) is pinned too: the
  handle is spent, the outcome refused, the receipt still queued. Two mutation probes confirm the assertions
  discriminate: substituting `engine2d_gpu_device_evidence_none()` for the
  authority's evidence drops the suite to 7/8, and deleting the
  already-redeemed check drops it to 7/8. The compatibility route is byte-for-byte
  unchanged and its routing-only receipt is pinned by a dedicated example. What
  remains: nothing here can distinguish a real fence from a fabricated record;
  that is the Vulkan-owner line, and the CUDA/Metal owners stay N/A.

---

## Agent N → `### Package 8 owner handoff`

Package 8's blocked-host ledger receipt is not reproduced here: agent N wrote it
as its own tracked document,
`doc/08_tracking/todo/egl_package8_host_capability_ledger_2026-09-12.md`, which
carries the delivered probe, its red→green selftest transcript, the measured row
set for this host, and the table of package-8 items blocked by fenced Codex
branches. Point the `### Package 8 owner handoff` section at that file.

---

## Agent Q → `## Parser variant build-plan follow-up (2026-09-08)` — PENDING, NOT INTEGRATED

Agent Q's package (`src/compiler/80.driver/parser_variant_cache_scope_v1.spl`,
its spec, and the `driver_aot_native_output.spl` scope-name extraction) is
**excluded from this branch**: it is red at `bd8df49e8d4` until Codex's parse
fix lands. Its spec cannot execute because
`src/compiler/80.driver/parser_variant_build_plan_v1.spl:89-92` reassigns a
local named `feature`, which the deployed compiler parses as the spec-DSL group
keyword; the whole module fails with
`parse: Unexpected token: expected Colon, found Assign`, so every consumer of
`ParserVariantBuildPlanV1` is blocked. The two-token fix (rename the local to
`feature_id`) is saved as
`scratchpad/parser_variant_build_plan_v1_feature_keyword.patch` and belongs to
that module's Codex owner. Q's full receipt paragraph, and the language bug it
raises (`feature` is a reserved spec-DSL group word:
`src/compiler/10.frontend/parser/test_analyzer.spl:132`), follow verbatim so
they are not lost when the fix lands.

2026-09-12, cache-join owner. `ParserVariantBuildPlanV1` already exists on the
EGL core base `bd8df49e8d4`
(`src/compiler/80.driver/parser_variant_build_plan_v1.spl`, Codex-owned) with
host execution identity kept separate from artifact/cache identity, exact
per-tier feature requirements from `environment_feature_registry_lookup_v1`
(baseline mask 1, v3 mask 3967), `X86_64V4` refused as
`UnsupportedTierV4`, and `compilation_executed=false` on every planned
artifact. It had zero consumers and zero specs. This session added the missing
join to the real native-build cache rather than a second contract:
`src/compiler/80.driver/parser_variant_cache_scope_v1.spl` (129 lines) derives a
per-variant `variant_identity` from the planned `cache_identity`, feeds it as a
capability word to the existing `native_build_cache_scope_key`
(`driver_build/incremental.spl:455`) and names the directory through the
existing owner, so two variants planned for the same triple, cpu text, backend,
optimization level and compiler identity can never share a scope while one
variant always reuses its own. `driver_aot_native_output.spl` was adapted by
extracting its own `"s" + sha256[0:32]` scope-name derivation into
`driver_native_build_cache_scope_name` (behaviour unchanged; the existing
`driver_native_build_cache_scope` now calls it) — the plumbing is selected, not
duplicated. `parser_variant_cache_reuse_admitted_v1` refuses cache reuse for a
variant whose `TargetCodegenReceiptV1` lacks artifact, emitted-feature, or
execution evidence, whose artifact identity does not match, whose emitted
feature word does not cover the tier requirement, or whose receipt architecture
is not x86-64 — each refusal named separately. Spec:
`test/01_unit/compiler/driver/parser_variant_cache_scope_v1_spec.spl`
(6 examples). Binary identity:
`/home/yoon/dev/simple/bin/release/aarch64-unknown-linux-gnu/simple`,
50093192 bytes, 2026-09-06 09:59:11. Measured on this host against the exact
files listed below: `6 examples, 0 failures` with the one-line blocker below
patched in and then reverted (re-measured after the final edit);
`6 examples, 2 failures`
before the scope derivation was moved off the process-derived compiler identity;
`test/01_unit/compiler/driver/backend_provider_cache_identity_spec.spl` 3/3;
`native_build_cache_plumbing_spec.spl` 12/27 both before and after the
`driver_aot_native_output.spl` edit (15 failures pre-existing at
`bd8df49e8d4`, unchanged by this work). No cache directory is created by this
module, so `scripts/check/check-cache-scope-ownership.shs` is unaffected and was
not run. What remains: the spec cannot execute at `bd8df49e8d4` because
`parser_variant_build_plan_v1.spl:89-92` reassigns a local named `feature`,
which the deployed compiler parses as the spec-DSL group keyword — the whole
module fails with `parse: Unexpected token: expected Colon, found Assign`, so
every consumer of `ParserVariantBuildPlanV1` is blocked. The two-token fix
(rename the local to `feature_id`) is saved as
`scratchpad/parser_variant_build_plan_v1_feature_keyword.patch` and belongs to
the module's Codex owner; it is the only occurrence of this pattern in `src/`.
Baseline/v3 SIMD admission proof (emitted bytes, artifact inspection, execution)
is not producible here: this host is aarch64 with no AVX2, so the admission
paths land as refusals only and the positive execution proof needs an x86_64
host.

### Agent Q — files (not integrated)
- `src/compiler/80.driver/parser_variant_cache_scope_v1.spl` (new, 129 lines)
- `src/compiler/80.driver/driver_aot_native_output.spl:669-676,721` (scope-name helper extracted + call site)
- `test/01_unit/compiler/driver/parser_variant_cache_scope_v1_spec.spl` (new, 6 examples)
- `scratchpad/parser_variant_build_plan_v1_feature_keyword.patch` (blocker fix, NOT applied — fenced file)

### Agent Q — bug to file (Codex-owned module)
`feature` is a reserved spec-DSL group word in the deployed compiler
(`src/compiler/10.frontend/parser/test_analyzer.spl:132`:
`["describe", "context", "feature", "scenario"]`). `var feature = X` parses, but
a later bare `feature = Y` is parsed as the start of a `feature "name":` block
and fails with `expected Colon, found Assign`. Minimal repro:
```
fn pick(flag: bool) -> u64:
    var feature = 3u64
    if flag:
        feature = 1u64
    feature
```
Either reserve the name consistently (reject the declaration too, with a
diagnostic naming the keyword) or stop treating a bare identifier statement as a
group-function call. Today the failure mode is a whole-module parse error with
no line number.

---

## Agent K → no plan-document section

CI wiring only; its red→green (`check-guard-wiring` 517→635 invoked, 725→607
baselined, 0 NEW unwired on both sides) is recorded in its commit message on
this branch.
