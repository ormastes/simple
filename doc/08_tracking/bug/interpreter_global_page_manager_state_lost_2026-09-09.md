# Interpreter loses global page-manager state across physical prefill

Date: 2026-09-09  
Status: fixed in source; focused bootstrap regression passes. Real-model cold
prefill now succeeds and qualification advances to an independent decode-COW
logical update failure.

## Qualified reproducer

Build the maintained llama.cpp fork containing the merged external-provider
ABI, then build the shim with that checkout. The shim gate must report 67
exports. Run `test/fixtures/slang_paged_kv_provider/owner_smoke.spl` with
`--no-jit` and the `ggml-org/tiny-llamas` `stories15M-q4_0.gguf` fixture.

The provider loads, negotiates capabilities, creates the physical pool, and
enters cold generation. `_cold_prefill` creates a logical request, reserves and
attaches its pages, and successfully validates the request immediately before
returning. The caller then rejects the same explicitly returned `KvRequestId`:

```text
OWNER_STAGE cold_generate
FAIL -- cold generation: logical request handle became invalid
OWNER_TELEMETRY requests=0 pages=0 hits=0 misses=1
```

Changing `_cold_prefill` from `Result<(), PagedExecutorError>` to
`Result<KvRequestId, PagedExecutorError>` does not preserve the manager state.

## Exclusions established

`request_handle_boundary_repro.spl` passes under the same interpreter when it
creates a request inside a `Result`-returning helper, performs reserve, update,
seal, and attach transitions, returns, validates the handle, closes it, rejects
the stale handle, and recreates it. Generic `Result` transport, helper scope,
and the logical lifecycle alone therefore do not reproduce the loss.

The installed Qwen3-Coder-Next fixture is not valid evidence for this issue: its
hybrid SSM memory is deliberately unsupported by the external paged provider.
The tiny conventional Llama fixture is the qualifying model.

The exact match-arm reproducer fails without any model or WFFI provider. A
normal dispatch helper placed between `find_prefix` and the selected match arm
also loses the mutation, so ordinary call entry is not sufficient to clear the
stale overlay. Two candidate fixes were built and rejected by the same focused
reproducer: publishing/repointing immediately before cloning the match arm, and
replacing scope-only block write-back refresh with `refresh_live_bound_globals`.
The latter cannot update this entry because its owner/global binding metadata is
already absent or inconsistent. Neither rejected change remains in source.

## Required diagnosis and acceptance

- Run the model-free regression's exact production shape: mutate the manager
  with `find_prefix`, then call the request-creating helper from the selected
  match-expression arm. Compare the ordinary-call control and same/imported
  module variants.
- Prove whether the global aggregate is overwritten, copied, or restored at the
  `_cold_prefill` return boundary.
- Trace where the caller's `PAGED_MANAGER`/`REPRO_MANAGER` overlay loses its
  owner binding; do not attempt another scope refresh until that metadata is
  proven present.
- Inspect the evaluator actually used by the admitted runtime. Candidate
  ownership boundaries are pure-Simple `eval_match_expr`/`env_assign` and
  call-method evaluation; the legacy interpreter's cloned `arm_env`, dirty
  copy-back, and owned-global resynchronization are diagnostic precedent only.
- Fix the compiler/runtime owner; do not inline the full lifecycle or weaken
  generation validation in the executor.
- Pass the model-free regression, the real cold request, and an exact-prefix
  repeat with observed hit/miss telemetry.
- Re-run cached-versus-uncached numerical parity before activation is enabled.

## Root cause and source fix

Unmarked entry globals were written only to the flat compatibility map, while
entry functions were tagged with the `<entry>` owner. Consequently
`sync_owned_captured_globals` found no owned-global target for the manager and
discarded the callee update. After registering entry globals under `<entry>`,
the newer store value was forwarded correctly, but the caller's older overlay
still shadowed its refreshed scope at match exit.

The fix has two generic parts:

- `record_flattened_global` assigns unmarked globals to `<entry>` and seeds the
  matching initial owner map.
- `copy_back_block_writes` refreshes bound global overlay copies, not only the
  scope pointer, before applying the block's dirty writes.

The exact model-free regression now passes with request creation, page
attachment, match-arm exit, helper return, close, stale-handle rejection, and
recreation intact.

## Real-model progression

With `SIMPLE_LIB` pinned to the isolated worktree, the 67-symbol provider shim,
and `stories15M-q4_0.gguf`, execution now completes logical request creation,
physical cold prefill, transaction commit, and prefix publication. It fails
later in `_decode_one` when `append_rows` follows physical COW commit. The
shared `LogicalUpdateFailed` enum initially made this look like cold occupancy
failure; a failure-only diagnostic at the cold update site did not fire.

The page-manager unit proved `commit_cow` itself replaces the request tail.
The production global owner nevertheless exposed the old sealed tail to the
next separate mutation call. COW publication, decoded-row accounting, and
sealing are now one owner-atomic page-manager operation. The real cold request
then completes and cleanup succeeds.

The remaining real-model failure is on the exact-repeat path immediately after
`fork_prefix`: the subsequent request-table read receives `InvalidRequest`.
This is the same class of global aggregate visibility defect at a second
mutation/read boundary, not a provider tensor or cache-identity failure. The
next fix must preserve the prefix fork as an owner-atomic operation or repair
the generic interpreter publication boundary; exact-repeat hit telemetry and
cached-versus-uncached parity remain required before activation.

A validated split create/attach API moved the failure from request lookup into
the attachment itself, proving that the separate global mutation boundary was
still stale. The page manager now provides `create_request_from_prefix`, which
validates the prefix, pages, capacity, and free generation-safe request slot
before publishing request state and reference increments in one direct,
non-nested owner operation. `fork_prefix` remains a compatibility wrapper.
Astra source review found no P0/P1 issue in that adjustment; real exact-repeat,
repeated-decode parity, and zero-owner shutdown evidence are still pending.

Runtime evidence then showed `create_request_from_prefix` returning a handle
whose request state was already absent at the immediately following
`request_page_count`. The generic cause is now pinned in identifier-receiver
method write-back: it updated the function frame and flat `MODULE_GLOBALS`, but
not the owner-indexed global store. Match-arm write-back refreshes from that
owner store and therefore restored the pre-call manager. The centralized method
write-back now publishes the mutated receiver through `set_owned_global` before
the arm can refresh. A compiler regression covers repeated `me` mutation of an
imported module global when the method call is the subject of a match expression.
That focused Rust regression passes. Its build used temporary copies of two
unrelated interpreter fallback definitions from their owning active lane; those
copies were removed immediately after the test and are not part of this change.

## Qualification result

A release-mode driver containing the owner-store fix now passes the real-model
Simple owner path with `stories15M-q4_0.gguf`: four-token cold generation,
four-token exact-prefix repeat, identical output, observed hit and miss
telemetry, zero active requests/reservations before shutdown, and inactive
owner/zero pool/no telemetry after shutdown. This exercises repeated physical
COW decode rather than only a one-token boundary.

The broader native qualification also passes the llama-backed real-provider
smoke and the synthetic provider ABI/state-machine conformance suite. Focused
Simple specs pass for engine physical-page configuration, backend capability
mapping, and inactive-owner lifecycle.
