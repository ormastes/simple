# Compiler Driver Layer Expert

MIR progress uses actual per-module fatal/context/ICE classification and the
common processed-minus-cached-minus-failed calculation. The logger's console,
events and snapshot share that calculation; a terminal failure reuses only
matching complete parent accounting. Unclassified or interrupted counts stay
unknown. The Windows logger diagnostic exceeded the cap before object output;
actual compiled reporting remains unqualified. See
`doc/08_tracking/bug/mir_progress_failed_modules_reported_success_2026_10_12.md`.

## Current bounded archive activation (2026-10-12)

The production controller owns a compilation generation before source loading,
then performs actual selected-source HIR transactions, journal publication and
genuine weave/current/mono/final issuance. MIR must consume the private final
repository in borrowed body scopes, retaining physical names and independent
logical specialization owners. Every new compilation resets the previous
generation after the native no-op fast path; cleanup revokes the final reader
only after MIR and code generation finish. Diagnostic publication must preserve
the original ordered counts, including failures already published by the real
validator or mono pass.

The initial orchestration admission targets managed native AOT, complete
streaming source inventories, enabled nonshard HIR cache and an explicit runtime
bundle. Actual ambient bootstrap routes retain their established semantics;
the full-native borrowed MIR consumer does not admit bootstrap-flat lowering.
Cold full-inventory and demand routes retain their existing owners. Routing is
derived after source loading and parsing publish the actual selection and
inventory; projected/nonstreaming routes require their own custody proof. Source review
and authored controls do not establish native activation or memory improvement.
Attempt13 compiled1,297 files and failed the extracted MIR field-type defect;
the incoming typed `field_type` correction awaits a fresh bootstrap. See
`doc/08_tracking/bug/phase2_matrix_strict_stage2_error_family_2026-10-09.md`.

Mission-critical V2 bootstrap/admission status is owned by
`doc/03_plan/sys_test/mission_critical_infra_hardening_v2.md`; its active owner
failure is `doc/08_tracking/bug/stage3_selfhost_exit_139_2026-08-14.md`.

## Role

Own source discovery, import closure, phase orchestration, execution-mode
selection, and compiler-driver performance under `src/compiler/80.driver/`.

## Source-loading invariant

- `Check` mode loads only the requested checking scope.
- `Interpret` mode keeps the explicit entry bounded and lets the interpreter
  module loader resolve imports lazily.
- Native entry-closure mode loads the transitive closure selected by
  `SIMPLE_NATIVE_BUILD_ENTRY` and suppresses whole-project bulk loading.
- The entry-closure collector excludes documentation fixtures beneath `/doc/`,
  but must retain explicitly imported executable modules under `src/app/doc/`.
  The regression is `driver_source_loading_spec.spl`'s application-doc closure
  case; do not broaden the exception to arbitrary documentation trees.
- Other project compilation modes may bulk-load the self-hosted compiler roots
  where their global compilation model requires it.

## Formal Verification 2.0 invariant

`CompileContext` retains `AssuranceStrictnessV2.Verified` while frozen V1
consumers conservatively project it to `critical`. A `verified` compilation
must not lower string-only direct calls and then claim a closed MIR/VIR path.
Until the frontend captures resolver `SymbolId` decisions and finalizes
`ResolvedDirectCallManifestV1` after complete MIR construction,
`CompilerDriver.lower_to_mir` must fail with
`FV2-E-CALL-MANIFEST-PRODUCER`. Do not weaken this to a name lookup or bypass
it with a bootstrap/entry-closure path; runtime and generated calls require an
explicit external-boundary model.

Do not reuse the native-only entry-closure environment flag as a shortcut for
interpretation: downstream HIR/MIR branches attach native/bootstrap semantics
to it. Keep the interpret exclusion explicit in
`driver_source_pipeline_loading.spl`.

## Performance evidence

The compiler-loader negative-cache and packed-byte performance handoff lives at
`doc/03_plan/sys_test/compiler_loader_script_crosslang_perf.md` (plan content
accepted; operational reconciliation pending; feature verification blocked).
Preserve its
distinction between facade failed-existence probes and filesystem syscalls, its
caller-sensitive cache key and reset generation, and its admitted-self-hosted
evidence rule. Live feature verification remains blocked by two distinct
prerequisites: the older deployed candidate's wrapper/help admission segfault,
and historical lane-A Stage3 context corruption after a clean 603-file parse.
Fresh r3 remains unproved: its first process was intentionally stopped before
Stage 2 admission so review corrections could be source-frozen; partial output
is not authority and no verdict/cycle was consumed. The latter is tracked at
`doc/08_tracking/bug/build11_stage3_compile_context_corruption_2026-08-14.md`.

For a one-file interpreted entry, measure wall time and max RSS through the
normal `bin/simple` command. A run that never reaches user code is source-loader
cost, not workload cost. Preserve the normal CPU guard; raising it is diagnostic
only and cannot be passing evidence.

Focused contract:
`test/01_unit/compiler/driver/interpret_lazy_project_sources_spec.spl`.
MCP end-to-end witness:
`test/02_integration/app/mcp_stdio_integration_spec.spl`.

Typed-storage native codegen freezes deep-copied module-qualified evidence
before cache lookup. The parent then creates class-handle MIR+storage capsules;
the builder callback sees only the frozen batch and module name. Revalidate
complete MIR/storage identity before and after codegen, bind object bytes and
size in the result receipt, and publish cache checkpoints only through the
parent completion hook. Do not call this real concurrency: the current
builder branch batches sequentially, and process workers need a complete codec.

## Separate RV64 Stage 3 MIR receiver corruption handoff (2026-08-14)

This is not the Build11 compiler-loader frontier above. The RV64 prerequisite
bootstrap reaches HIR with zero errors, then its
Stage 3 log ends in MIR method-call lowering with an impossible receiver local
ID. Inspect `method_calls_literals.spl` receiver resolution/writeback and the
`value_struct_layout.spl` push-heavy caller shapes. Do not claim the direct
`CompileContext.error_count_value` reads fixed the root cause; require an exact
native reproducer, adjacent aggregate/method-call regression, and a fresh
Stage 4 essential-tools receipt. Tracking:
`doc/08_tracking/bug/stage3_selfhost_post_hir_segfault_2026-08-14.md`.
## Restart12 bootstrap/deployment status (2026-08-14)

The current Stage 2 compiler is bootstrap-only. The static-owner receiver
frontier is repaired; a later GDB run proved the next Stage 3 exit 139 at
aggregate `HirType` transport from `maybe_copy_array_value` into
`remember_local_hir_type`. Keep that metadata owner-local and cross the helper
boundary with scalar source/destination IDs. The focused native regression is
green, but Stage 3/4 remain unadmitted, so do not advertise SPipe, deployment,
or release admission. Current owner and resume condition:
`doc/08_tracking/bug/stage3_post_file_copy_exit139_2026-08-14.md` and the
canonical deployment plan.

Phase-1 source loading owns closure COMPLETENESS, and its line cursor mixes
units: `text.len()`/`text[a:b]` are byte-indexed, `char_code_at` is
char-indexed. `_driver_line_end` now returns a `(byte, char)` pair and both of
its callers advance both cursors together; do not reintroduce a single cursor.
A truncated closure does not fail here — it fails much later in HIR as
`unresolved type`, attributed to the wrong file. Verify closure size at
`[build] source_closure N/N` before believing any HIR error attribution.
See `doc/08_tracking/bug/simpleos_wm_vulkan_cross_arch_rows_blocked_2026-08-31.md`.

- 2026-09-05 gpu_frontend_offload: default-off frontend offload switch (`structural_contracts/frontend_offload_switch.spl`, driver gate in `80.driver/driver_source_pipeline_parsing.spl`) — see `doc/00_llm_process/feature_expert/gpu_frontend_offload/skill.md`.

## Phase 3 archive publication journal (2026-10-12)

The inactive `cache/driver_hir_archive_journal_v1.spl` owner records actual
registration calls and logical alias events. Publication failure retains the
pending event and closes registration without minting a successful schedule.
Owned verification scopes reclaim cumulative metadata scratch. The native
`journal` fixture requires 13 checks and the canonical managed runtime/tool
authority. These checks remain unrun; production admission still requires the
actual surface visit order, distinct layout order and post-HIR transformed-body
prerequisites.

`cache/hir_mono_verification_use_v1.spl` independently replays immutable actual
applied selections and produces a fresh real verifier report (`verification`,
18 native checks pending). `cache/driver_hir_post_validation_fact_lease_v1.spl`
reads full original bodies inside borrowed leases, yielding body-free DTOs
(`postfacts`, 26 native checks pending). Production owners must bind actual
ordered indexes, RT capabilities and transformed parents; these helpers alone
do not activate the pipeline or grant final admission.

`cache/driver_cold_hir_source_capture_plan_v1.spl` performs actual pinned SCV
generation, snapshot, canonical generation text, selected-source, full-inventory
CFG and count checks in one owned inventory scope. Only first-physical-source
capture input rows escape. The retained cold typed-receipt helper shares the
same source validators at its original check points, preserving first-physical
deduplication and independent ABI failure collection. The new source factory is
inactive and does not publish ctx receipts or admit transformed bodies; four
new boundary examples and full SCV/native integration remain unrun.

The retained full-inventory emission loop now calls
`cache/driver_cold_hir_emission_lease_v1.spl` after complete typed ABI receipt
collection. Its owned wrapper promotes the fresh emission/failure Result and
cache diagnostic owner; it preserves the prior cache warning alias and never
promotes the input HIR. The archive module helper
uses the same actual borrowed emitter/witness implementation. All-success ctx
publication and original error categories remain; two new compiled examples
are unrun. This is scoped retained-path emission, not full pipeline activation.

`cache/driver_hir_archive_schedule_v1.spl` and the actual CompilerDriver capture
wrapper replay the frozen streaming surface/source owner, independent authored
aliases, shared visit producer and separate physical layout schedule. A shard's
all-source recipe cannot admit full publication. The `schedule` and
`schedule_shard` native selectors each require 13 checks in a fresh runtime
process; both remain unrun. Aspect policy replay now accepts explicit actual
ordered claim DTOs without registry mutation. Genuine source/policy and
transformed-body ownership remains required before production activation.

Distinct `mono_archive_current_body_v1` frames and fresh current registration
preserve the unresolved original parent instead of reusing stale declarations.
The actual publisher rereads full current bodies and recollects their rows.
The `current-registration` selector requires 13 native checks, still unrun.
Explicit aspect/layer/effect/RT claim replay avoids installing another
compilation's registries; the real driver still must capture and bind all actual
source/policy inputs. Borrowed MIR lowering uses the existing complete lowering
implementation and leaves scope/output promotion to its caller. These are
inactive mechanical prerequisites, not a final repository or admission token.

`cache/driver_cold_hir_weave_body_v1.spl` reads a separate complete
`post-hir-weave-v1` artifact for cold ABI/SMF/witness capture before optional
quiet resolution. It shares the byte grammar with strict current mono bodies
without changing their resolved-stage bytes/key/API. The `weave-cold` selector
requires 14 actual-body native checks, unrun. The real driver prerequisite owner
must authenticate both stage boundaries and the original returned cold capture.

The post-HIR `*_selected_in_owned_scope_v1` readers accept actual captured-policy
walker selection. Ambient wrappers remain unchanged, and global/local HAL
overrides remain mandatory. The `postfacts` selector now hashes all three real
fixture source files and requires 26 native checks, still unrun. Selection flags
alone grant no accepted policy or stage ownership.

`cache/driver_hir_post_validation_policy_v1.spl` and its once-only real driver
bridge capture actual ordered claims and pre-consumption capabilities under the
verified full schedule/journal. Aliases retain their independent authored paths
while proving the genuine earlier canonical body and physical bytes. The
`postpolicy` selector requires 22 checks and the exact managed tool/runtime
handoff, still unrun. Actual complete gates, weave and cold/quiet stage use must
be independently replayed before production or final admission.

`cache/driver_hir_weave_source_policy_v1.spl` replays actual frozen physical
source through the selected frontend with fresh isolated claim registries,
then restores the original registry roots before scratch closes. It checks
complete source-produced rows and retains only actual frontend/CFG metadata;
it does not consume or reinstall the next RT capability manifest. The five
added source/custody controls are unrun and grant no final admission.

The complete current-body input now reaches the shared mono root/FIFO,
assembly and immutable full-verification recipe consumers. Current-mode inputs
refuse missing frames/cache or stale original-body publication identities;
original-mode recipes keep their existing bytes. `current-mono` requires 20
native checks, unrun. Registration schemas, identity and current seal are
extracted below the 800-line limit; the facade preserves its public API and
the unchecked installer stays private. This mechanical replay still requires
the genuine driver prerequisite and final repository owner before MIR use.

## 2026-09-26 — `native-build` restored: backend table in the interpreted worker, entry-file hashing, module-init reads

- **The interpreted native-build worker never installed the static backend
  table.** Since the K1 migration only the compiled CLI entries install it, and
  the worker cannot `use compiler.driver.bootstrap_k1_selected` — under the
  interpreter that module path resolves to the fail-closed stub
  (`src/compiler/80.driver/bootstrap_k1_selected.spl`), so every build died
  with SIGILL (`ud2`) at codegen entry. The worker now imports the committed
  composition by path,
  `use compositions.kernel_llvm_cranelift.compiler.driver.bootstrap_k1_selected.{...}`
  ([native_build_worker.spl](../../../../src/app/cli/native_build_worker.spl) :10-13, `a5158762598`).
  Record: [native_build_worker_sigill_ud2_at_codegen_entry_2026-09-26](../../../08_tracking/bug/native_build_worker_sigill_ud2_at_codegen_entry_2026-09-26.md).
- **`--output-format both` hashed the `--source` DIRECTORY, not the entry
  file.** `dynload` (the default mode) selects `Both`, so every default
  native-build hit it the moment `file_read_result` became fail-closed.
  `_driver_entry_source_input`
  ([driver_aot_pipeline.spl](../../../../src/compiler/80.driver/driver_aot_pipeline.spl) :65)
  now picks the first `is_file` input for the SMF manifest hash (:193-198).
- **Module-level values land in `.bss` and are filled by a generated
  `__module_init_*` that freestanding consumers never call**, so an unguarded
  `slot[0]` on a module-level array can index an EMPTY array in natively
  compiled code. Every `lex_env_save_enabled[0]` read in `lexer.spl` now goes
  through the length-checked `bool_slot0_or` / `lex_env_save_on`
  ([lexer.spl](../../../../src/compiler/10.frontend/core/lexer.spl) :93 / :105,
  `a6aea23798f`). Same defect class as
  [simple_module_const_scalars_need_runtime_init_on_baremetal_2026-09-19](../../../08_tracking/bug/simple_module_const_scalars_need_runtime_init_on_baremetal_2026-09-19.md);
  record [stage2_candidate_env_lexer_array_oob_sigill_2026-09-26](../../../08_tracking/bug/stage2_candidate_env_lexer_array_oob_sigill_2026-09-26.md).
  Until the driver guarantees `__module_init_*` runs for every consumer, treat
  every module-level container read in compiler code as possibly-empty.

Production archive activation begins a fresh generation after the no-op fast
path, selects eligibility after actual source selection, and revokes the owner
after every compilation result. An attempted or revoked archive owner cannot
fall back to retained HIR in the MIR consumer. Native qualification remains
pending; source checks alone do not establish compiler or runner admission.

Generic archive signatures retain declaration linkage metadata in digest v2.
Driver archive transport must preserve this field through specialization;
caller display qualifiers cannot establish the native callee owner. The
source-reviewed repair requires a fresh generation for native qualification.
