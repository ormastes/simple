# Feature: X25519MLKEM768 acceleration

## Raw Request

`$sp_dev impl X25519MLKEM768 for cpu, simd, gpu. version. make unittest branch coverage almost 100%. find free module compare in outs. 3 set of tests. research and tests, x86,arm,riscv simd each, cuda,vulkan,metal. configs on same data. do more research and design and check perf bug also.`

## Task Type

feature

## Refined Goal

Implement a versioned, pure-Simple X25519MLKEM768 TLS 1.3 hybrid key-exchange capability with a scalar CPU oracle, honest x86/ARM/RISC-V SIMD and CUDA/Vulkan/Metal acceleration lanes, identical-fixture cross-backend comparison, production TLS integration, near-complete branch coverage, and measured performance-regression evidence.

## Acceptance Criteria

- AC-1: A public versioned `X25519MlKem768Config` and result/evidence API identifies the current standardized ML-KEM-768 parameter set, TLS NamedGroup code point, wire encoding order, implementation version, requested target, resolved backend, and fallback or rejection reason.
- AC-2: The scalar CPU implementation completes deterministic key generation, encapsulation, decapsulation, implicit rejection, X25519 combination, and malformed-input handling against official NIST ML-KEM vectors plus at least one independently maintained free/open implementation.
- AC-3: TLS 1.3 client and server negotiation advertise, parse, select, and derive secrets for X25519MLKEM768, prefer it according to configuration, retain explicitly configured classical interoperability, and fail closed on malformed shares, downgrade inconsistencies, and hybrid-secret errors.
- AC-4: x86, ARM, and RISC-V SIMD lanes use the shared public interface and the exact same fixtures as the scalar CPU oracle; executable lanes prove independent accelerated execution and byte-identical outputs, while unavailable native hosts remain explicit blocked rows with resume commands.
- AC-5: CUDA, Vulkan compute, and Metal lanes use the shared public interface and exact same fixtures; each PASS requires compile, submit, completion/fence, device-origin readback, backend identity, and byte-identical CPU-oracle output, while unavailable hardware remains an explicit blocked row rather than a skip or CPU-mirror PASS.
- AC-6: One configuration matrix drives scalar CPU, SIMD ISA, and GPU backends with `suggest` and `require` semantics; `suggest` records honest fallback and `require` fails closed when the requested capability is absent.
- AC-7: Three independently useful test sets exist: official/absolute cryptographic known-answer and negative unit tests; identical-fixture CPU/SIMD/GPU cross-backend tests; and TLS 1.3 negotiation/interoperability/system scenarios with readable generated SPipe manuals.
- AC-8: Owned X25519MLKEM768 implementation code reaches at least 98% measured branch coverage, with 100% coverage of security-critical validation, implicit-rejection, backend-selection, fallback, and fail-closed branches; any mechanically unreachable branch is justified in the coverage report rather than excluded silently.
- AC-9: Baseline and post-change benchmarks report keygen, encapsulation, decapsulation, hybrid-combine, and end-to-end handshake latency plus throughput and max RSS on the same fixtures; material regressions are fixed or recorded as concrete tracked bugs with measurements.
- AC-10: Secret-dependent production paths avoid secret-indexed lookup, early-exit equality, secret-dependent backend selection, and secret-bearing diagnostics; constant-time behavior and zeroization limitations are documented and tested where observable.
- AC-11: Research compares applicable free/open implementations and standards; requirements, NFRs, architecture, detail design, test plan, agent-task plan, guide, generated manuals, and performance report all use the `x25519mlkem768_acceleration` slug or an explicit alias.
- AC-12: Focused lint, duplication, direct-runtime guards, relevant core/lib/MCP smoke gates, generated-spec layout guard, and production-readiness verification pass with no stubs or placeholder GPU artifacts.

## Scope Exclusions

- Repository release, version bump, tag, or push is not implied by the word `version`.
- ML-DSA certificate signatures and non-TLS protocols are outside this feature except where research documents future compatibility.
- Emulation, CPU mirrors, emitted source alone, or cached third-party results do not count as native SIMD/GPU execution evidence.

## Cooperative Review

- Sidecars: local crypto/TLS audit; standards and free/open implementation comparison; SIMD/GPU processing-backend and host-capability audit.
- Merge owner: `/root` primary Codex agent.
- Final reviewer: `/root` highest-capability Codex pass after all sidecar findings are merged.
- Shared interfaces: `X25519MlKem768Config`, `X25519MlKem768Backend`, `X25519MlKem768Evidence`, `x25519_mlkem768_keygen`, `x25519_mlkem768_encapsulate`, `x25519_mlkem768_decapsulate`, `x25519_mlkem768_combine`, `x25519_mlkem768_resolve_backend`.
- Manual flow steps: `Load the shared X25519MLKEM768 fixture`; `Run the scalar CPU reference exchange`; `Compare SIMD ISA results with the CPU oracle`; `Compare GPU results with the CPU oracle`; `Negotiate the TLS 1.3 hybrid group`; `Measure the backend performance budget`.
- Setup/checker helpers: `setup_x25519_mlkem768_fixture`, `check_backend_against_cpu_oracle`, `check_tls_hybrid_transcript`, `check_x25519_mlkem768_perf_budget`.
- Any placeholder for these helpers must use `assert(false)` or `fail(...)`; silent no-op helpers are forbidden.
- Generated-manual review owner: `/root` primary Codex agent.

## Runtime Boundary Decision

- `runtime_need`: established and implemented for canonical typed-array SIMD dispatch, owned coverage-report text conversion, and compiler/runtime branch-probe ABI alignment.
- `facade_checked`: complete for `std.simd`, the crypto-owned CUDA/Metal sessions, canonical no-GC synchronous SFFI owners, and compiler/test-runner coverage owners; no ProcessingIR or graphics-engine shortcut is appropriate for cryptographic NTT work.
- `chosen_path`: `reuse-facade`; extend the existing SIMD/runtime and crypto-session owners, with no feature-local raw FFI boundary.
- `rejected_shortcuts`: raw feature-local `rt_*` aliases, fixture-only acceleration branches, CPU mirrors labeled as GPU/SIMD execution, direct backend field pokes, and generated-source-only PASS claims.

## Phase

implementation-active

## Log

- dev: Created state file with 12 acceptance criteria (type: feature).
- dev: Recorded concurrent-work rule; this lane owns only new/explicit X25519MLKEM768 artifacts and must not absorb unrelated dirty files.
- research: Merged local crypto/TLS, acceleration, and standards/free-module sidecars; `/root` reviewed the combined findings.
- research: Wrote local/domain research plus feature/NFR options. Awaiting required user selection before final requirements, design, or implementation.
- requirements: User selected Feature D + NFR B on 2026-08-02.
- requirements: Wrote final feature/NFR requirements and deleted unchosen option documents.
- design: Drafted architecture, detail design, system-test plan, agent-task plan, and TLDR companions using the frozen interfaces and D+B promotion policy.
- design: Merged and accepted TLS, backend, and test/coverage/performance sidecar reviews. Added typed alerts/entropy, attempt-level evidence, stable-ID branch coverage, crypto-owned persistent GPU providers, canonical fixture manifest, and exact capability runner contract.
- impl: Added the backend-neutral config/evidence/result contract, scalar-only fail-closed resolver, scalar hybrid keygen/encapsulate/decapsulate/combine boundary, and strict TLS group/share validation.
- impl: Removed unconditional X25519 ladder diagnostics and replaced secret-bit conditional swaps with mask-based limb swaps so future performance evidence has a hardened scalar baseline.
- impl: Added distinct unit, backend-matrix integration, TLS system, and performance spec entrypoints plus matching manuals and a canonical fixture manifest.
- impl: Added checked ML-KEM-768 boundaries (canonical public-key encoding, embedded secret-key hash validation, exact sizes, and implicit rejection), a shared four-lane SIMD NTT/INTT primitive, and deterministic official-ACVP plus pinned `mlkem-native` digest fixtures.
- impl: Wired real hybrid-first TLS client/server negotiation for NamedGroup `0x11EC`, strict 1216/1120-byte shares, typed alerts, independent entropy, 64-byte X25519||ML-KEM secret ordering, downgrade rejection, and explicitly configured classical fallback.
- impl: Specialized AVX2/NEON/RVV and CUDA/Vulkan/Metal resolvers remain deliberately unpromoted: the shared SIMD primitive is not yet a complete measured ML-KEM backend and no crypto-owned native GPU provider exists. `require` therefore fails closed and `suggest` records scalar fallback.
- perf: Added the benchmark specification (2 warmups, 30 samples, p95) but did not claim measurements; native SIMD/GPU host rows, max RSS, and end-to-end handshake evidence remain blockers.
- coverage: Added branch-focused negative and resolver cases, but the required >=98% measured branch report is blocked until a stable self-hosted compiler/test runner is available.
- verify: A diagnostic check through `build/bootstrap/repair-full/.../simple` disclosed that it delegates to the Rust bootstrap seed and timed out; it is explicitly not accepted as verification evidence.
- verify: A concurrently produced pure-Simple stage-3 compiler identified itself as self-hosted, but raw unit-spec compilation lacked SPipe built-ins and compiling the hybrid module terminated with signal 11 after unresolved MIR method diagnostics (`.merge`, `.to_i64`, `.to_u64`, `.to_u8`). This matches the existing `doc/08_tracking/bug/mir_unresolved_method_const0_fails_open_2026-07-28.md` compiler lane; no PASS is claimed and the unrelated compiler/runtime worktree was not modified.
- verify: Zeroization evidence, native x86/ARM/RISC-V/CUDA/Vulkan/Metal execution, >=98% measured branch coverage, performance budgets, and the full production-readiness gate remain open.
- review: Confirmed against current `draft-ietf-tls-ecdhe-mlkem-05` that X25519MLKEM768 intentionally encodes ML-KEM before X25519 for both shares and for the combined secret despite the group name.
- review: Corrected the FIPS encapsulation-key check to validate all three 384-byte encoded polynomials and reduce raw 12-bit coefficients modulo q before constant-time re-encoding comparison; the prior draft check would have rejected every valid 1184-byte key.
- review: Removed the remaining secret-dependent ladder-bit loop/branch in the small-limb X25519 path and updated both legacy TLS unit-test trees plus generated matcher copies for the expanded constructors.
- verify: One-time direct-runtime audits: staged PASS; working-tree FAIL is solely the unrelated concurrent `src/app/build/cli_entry.spl` direct `rt_process_run` edit. Generated-spec layout count is 0 and the scoped diff whitespace gate passes.
- impl: Added a fail-closed production entropy owner backed by the canonical no-GC synchronous platform-attestation wrapper. Hybrid client/server TLS now rejects unavailable, malformed, oversized, or catastrophic all-zero entropy before emitting protocol output; deterministic candidate validation is exposed only through an explicitly named test helper.
- impl: Threaded the SIMD NTT/INTT path through complete ML-KEM-768 keygen, encapsulation, re-encryption, implicit rejection, and decapsulation candidate APIs. The shared path uses eight i32 lanes when native AVX2 is reported and four lanes for the NEON/RVV candidate lowering.
- impl: Added evidence-only AVX2/NEON/RVV hybrid candidate entry points using the same config and fixtures as scalar. Production resolution remains deliberately unpromoted; candidate evidence cannot masquerade as a production backend and leaves execution-proof digest/invocation evidence unset.
- test: Expanded absolute entropy-policy branch tests and full scalar-vs-SIMD ML-KEM/hybrid differential tests. Native AVX2 executes only on an AVX2 host; NEON/RVV unavailable hosts prove fail-closed behavior while their native rows remain blockers.
- research: Current host exposes NVIDIA RTX A6000 and TITAN RTX CUDA devices plus two physical NVIDIA Vulkan devices; llvmpipe is separately identifiable and cannot count as native evidence. Metal remains unavailable on Linux.
- architecture: Applied the SFFI boundary rule for the GPU lane: future CUDA/Vulkan/Metal providers must reuse canonical no-GC sync wrappers and persistent executors rather than add feature-local `extern fn` declarations.
- verify: The pure-Simple stage-3 compiler still fails during MIR lowering when compiling the new entropy boundary because imported existing code triggers unresolved `.merge`/conversion methods. This is the same tracked compiler blocker; syntax reached MIR but no compile PASS is claimed.
- gpu: Added a real batched FIPS-203 forward-NTT PTX kernel, a persistent Simple CUDA executor using the canonical `CudaSession`/CUDA SFFI owners, exact-size upload/submit/sync/readback, device identity, artifact digest, invocation evidence, and best-effort secret-buffer clearing.
- gpu: `ptxas 13.0.88` assembled the PTX successfully. An independent CUDA Driver API probe JIT-loaded the exact source, executed a three-polynomial identical fixture, synchronized, read back all 768 coefficients, and matched an independent scalar NTT on both NVIDIA RTX A6000 (sm_86) and TITAN RTX (sm_75). Repro command is `scripts/check/check-x25519mlkem768-cuda-ntt.shs`; hashes and device receipts are frozen in the fixture manifest.
- gpu: Extended the exact PTX artifact and independent Driver API probe with FIPS-203 inverse NTT. Forward and inverse batches compile, submit, synchronize, read back, and match the independent scalar oracle on all 768 coefficients on both NVIDIA devices. The persistent Simple provider exposes both entries through one cached CUDA session.
- architecture: Replaced the provisional Engine2D session dependency with the crypto-owned `CryptoCudaSession`, which wraps canonical CUDA facades without raw feature-local FFI and owns persistent context/module lifecycle, transfer, launch, synchronization, identity, and cleanup.
- gpu: This is native CUDA NTT/INTT evidence only, not full ML-KEM GPU promotion. Remaining ML-KEM composition, persistent performance evidence, Vulkan repair, and Metal remain open.
- gpu: Added a Vulkan GLSL forward-NTT candidate and an independent physical-device harness with device-local input/output buffers, staging upload/readback, compute pipeline, descriptor bindings, push constants, explicit transfer/compute barriers, fence wait, and llvmpipe exclusion. GLSL compilation and `spirv-val` pass.
- gpu: Vulkan execution is RED: optimized and unoptimized SPIR-V produce the same coefficient mismatch on both physical NVIDIA devices (first mismatch index 2, expected 1970, actual 3323). The three-cycle cap was reached; details and resume criteria are recorded in `doc/08_tracking/bug/x25519mlkem768_vulkan_ntt_barrier_mismatch_2026-08-02.md`. No Vulkan PASS or promotion is claimed.
- gpu: Added a Metal Shading Language forward/inverse NTT artifact and a native Swift/Metal compile-dispatch-wait-readback probe over the identical three-polynomial fixture. The Linux host cannot execute Metal; the manifest records BLOCKED with resume command `scripts/check/check-x25519mlkem768-metal-ntt.shs` and frozen source/probe/script hashes.
- gpu: Composed complete ML-KEM-768 keygen, encapsulation, decapsulation, FO re-encryption, and implicit rejection through the narrow `MlKemNttBatchProvider`. The CUDA candidate reuses one persistent crypto session and batches transforms into 1/2/4 kernel invocations respectively; production dispatch remains unpromoted pending executable Simple differential tests and performance gates.
- perf: Removed a CUDA hot-path allocation defect: the executor now retains capacity-sized host/device/argument buffers across the complete exchange, grows them only when required, and zeroes them between operations and at teardown. The differential test requires one context/module generation, seven total kernels, and retained 6144-byte capacity across keygen/encaps/decaps.
- perf: Metal uses the same persistent-capacity policy through `CryptoMetalSession`: one device/queue/shader/two-pipeline generation and retained zeroized buffers. Its complete 1/2/4-launch differential row is executable on a native macOS host but remains BLOCKED here.
- refactor: Consolidated scalar, SIMD, CUDA, and Metal K-PKE execution through one `MlKemNttBatchProvider` algorithm body. `ml_kem_kpke.spl` is 798 lines, below the selected 800-line NFR cap, and backend-specific cryptographic duplication was removed.
- verify: A distinct pure-Simple `bootstrap-segv-fix` stage compiler exposed and enabled repair of a malformed Metal provider inline conditional. A second bounded compile parsed the full hybrid dependency closure, then crashed with signal 11 in the existing self-host compiler lane; no third identical retry was attempted.
- oracle: Pinned the complete 4,704-byte ML-KEM-768 output set from `mlkem-native` commit `fd58ec75` in a normalized SDN fixture. The absolute test now compares every encapsulation-key, decapsulation-key, ciphertext, and shared-secret byte, not only their SHA-256 summaries.
- oracle-validation: Independently decoded the normalized fixture and confirmed exact lengths 1184/2400/1088/32 plus SHA-256 values `c45a699a...c247`, `1dc4ab01...af39`, `0b99b2af...4743`, and `340f07be...f596`; malformed, truncated, odd-length, invalid, and uppercase hex parser branches are covered.
- perf-gates: Replaced the weak p95-positive-only predicate with all-sample validation, p50/p95/p99 and throughput reporting, and exact executable boundary checks for the 5% scalar regression, 1.5x SIMD, and 1.25x GPU gates. Native measurements and RSS/device-memory receipts remain blockers.
- provider-hardening: Added deterministic CUDA/Metal tests for invalid input, missing CUDA artifacts, and post-shutdown reuse. Metal now rejects batches above 65,535 before allocation and exports symmetric forward/inverse candidate wrappers.
- compiler-blocker: The pure-Simple stage3 compiler parsed the updated Metal provider and dependency closure, then crashed with exit 139 before emitting the module. This reproduces the existing self-host compiler failure; no Rust-seed fallback or repeated retry was used.
- traceability: Corrected stale scenario labels to the selected requirements. Every `REQ-001` through `REQ-016` now maps to at least one executable scenario; raw feature-local `rt_bytes_u8_at` use was removed from the hybrid module in favor of typed byte indexing.
- runner-audit: Located a full pure-Simple CLI that type-checks all feature modules, but its run/compile subpaths delegate to the Rust seed despite no-delegate flags. Seed execution passed 15/17 unit scenarios and failed both encapsulation scenarios through the known seed class/trait value model; these results are diagnostic only, not product PASS evidence.
- compiler-workarounds: Removed seed-fragile multiline conditional-value bindings from ML-KEM and replaced tuple indexing with destructuring after native compilation exposed `undefined identifier: c` followed by empty-tuple HIR inference failure. Updated owned imports from deprecated `std.ffi.io` to `std.sffi.io` and boolean-negative assertions to canonical `expect_not`.
- pure-probe: Added a normal-Simple, no-SPipe oracle probe with pinned `mlkem-native` key/ciphertext/secret digests. Pure `check` passes. Its isolated Cranelift native-build exits 132 after resolving `ml_kem` and `sha256`, with `field access on nil receiver`; the traced two-cycle blocker and exact cache/resume lane are recorded in `x25519mlkem768_pure_native_probe_closure_nil_2026-08-02.md`.
- compiler-workaround: GDB localized the stage-3 nil receiver to the first `ParserModule` field read after a struct-valued Dict lookup. The existing low-memory streaming-surface route bypassed that transport and reached HIR in 2.4 seconds. Its final bounded attempt exposed two remaining empty-tuple index sites; all owned ML-KEM/probe tuple reads were converted to destructuring and both files pass pure `check`. Native oracle execution remains unclaimed because the three-cycle cap is exhausted.
- compiler-workaround: Extended the empty-tuple fix through the scalar, SIMD, CUDA, and Metal hybrid entry points. `ml_kem.spl`, `hybrid.spl`, and the ordinary oracle probe each report `OK` from the pure-Simple checker; command status remains nonzero only because the repository-wide hygiene gate finds an unrelated concurrent file.
- runner-audit: A newly appeared, independently rebuilt pure `simple-stage3-u32fix3` binary was tested in an isolated cache. Direct and fully gated low-memory streaming invocations both exited 139; GDB showed the identical `module_surface_from_module` -> `module_surfaces_from_modules` aggregate-transport crash. Its three-cycle audit is exhausted and it is not an admitted runner.
- coverage-readiness: Added per-owner `# @cover` thresholds to all four focused specs, removed empty success-arm `pass` statements, added malformed checked-ML-KEM and hybrid public-boundary cases, candidate resolver validation, malformed/unexpected TLS shares, complete scalar ServerHello decapsulation, and all-zero X25519 alert mapping. Tuple-index lowering hazards were removed from the focused specs.
- evidence-ledger: Added `doc/09_report/x25519mlkem768_acceleration_evidence_2026-08-02.md`, explicitly separating native PASS, FAIL, BLOCKED, and missing coverage/performance receipts. No numeric coverage, performance promotion, or full backend PASS is claimed.
- perf-readiness: Added a 30-sample complete scalar hybrid-exchange benchmark and a fail-closed native/RSS harness. The harness rejects Rust-seed runners, fallback/skip output, missing/nonpositive percentiles or RSS, absent trustworthy baseline receipts, and scalar warm-p95 regression over 5%.
- perf-calibration: The scalar/RSS harness deliberate-negative self-test rejected the current Rust bootstrap seed before test execution with `reason=rust_seed_not_admitted`; no timing result was fabricated.
- backend-audit: The NTT candidate genuinely invokes `std.simd` x4/x8 APIs, but neither admitted pure-Simple native backend implements them: C and LLVM lowering explicitly panic as unsupported, the stdlib Wave 2 integer dispatcher forces scalar fallback, and no RVV implementation/VLEN strip-mining path exists. The excluded Rust bootstrap has AVX2/NEON intrinsics but documents incomplete compiled vector marshalling. AVX2/NEON/RVV are therefore FAIL implementation rows rather than completed candidates awaiting only host evidence.
- cpu-simd-impl: Replaced the blocked generic-vector ABI with a canonical typed-array runtime façade. The live production C owner now dispatches ML-KEM forward/inverse NTT butterflies to AVX2 x8, NEON x4, or VLEN-agnostic RVV, returns a fresh tagged array, and exposes backend/hit receipts. The CPU provider batches complete polynomial vectors through one call; candidate operations fail if no vector chunks execute.
- cpu-simd-evidence: `check-x25519mlkem768-cpu-simd.shs` compiled the live runtime and matched all 768 forward/inverse coefficients against an independent scalar oracle. Native x86_64 AVX2 recorded 240/480 hits. AArch64 NEON QEMU recorded 576/1152 hits. RVV QEMU passed at VLEN 128/256/512 with 4/8/16 e32m1 lanes. QEMU rows are correctness-only.
- perf-finding: The bounded 10,000-iteration three-polynomial benchmark measured 5,055 ns scalar versus 4,618 ns AVX2 per polynomial (1.095x), below the selected 1.5x gate. Promotion remains prohibited; scalar modular reduction and boundary scratch/allocation costs are tracked in `x25519mlkem768_avx2_ntt_scalar_reduction_perf_2026-08-02.md`.
- coverage-compiler: Added stable authored-path/full-span/kind IDs, compiler-owned zero-count manifests, and runtime probes for MIR conditionals plus switch arms/defaults. Added zero-executed, deliberate-red, exact-edge, same-line cross-file, and multi-child calibration scenarios. Numeric coverage remains pending an admitted source-matched pure runner.
- coverage-abi: Repaired the canonical coverage façade to the runtime `(id,result,file,line,column)` ABI, added owned C-string-to-Simple report conversion with exactly-once native free, corrected the SFFI/test-runner dump owners, and added a core-C owned-text self-check. The self-check passed; the first strict compile attempt exposed an unrelated pre-existing ignored-`write` warning, and the bounded second attempt passed without `-Werror`.
- perf-repair: Replaced AVX2 per-lane `% 3329` with exact reciprocal reduction and count-sized heap scratch with bounded wiped polynomial scratch. Exhaustive comparison of all 22,157,825 reachable signed intermediates reported zero mismatches. The prior SIMD wrapper retry cap prevents a same-session NTT/performance rerun, so the 1.5x promotion gate remains open.
- coverage-cache: Added coverage mode to the native object-cache scope so a manifest-bearing build cannot reuse non-instrumented objects. Added a source contract spec and mirrored manual note.
- coverage-capsule: Added the owned-report conversion self-check to the core-C capsule producer and receipt contract; shell syntax passes. The full capsule run remains deferred because its intentional runtime-clean guard rejects this active dirty feature lane.
- provider-contract-audit: Confirmed complete CUDA and Metal candidates already reuse one executor across the 1/2/4-operation keygen/encapsulate/decapsulate sequence, with seven cumulative calls, one generation, retained 6144-byte capacity, and identical scalar inputs. Added a hardware-independent recording scalar provider scenario that asserts the exact forward batches `[6,3,3,3]`, inverse batches `[4,1,4]`, and byte-identical keys/ciphertext/secrets through the same production provider composition. The focused checker is presently blocked before the owned file by an unrelated concurrent `parser_stmts.spl` `TripleLt` parse error; no execution PASS is claimed.
- perf-static-audit: Removed the inverse NTT's final 256 scalar `% 3329` operations on AVX2. The new eight-lane scale-by-3303 loop reuses the exhaustively validated reciprocal reducer. Current-source `-O2` compilation passed and disassembly contains vector multiply/reduction with no divide instruction. This is assembly-shape evidence only; the capped complete correctness/performance wrapper was not rerun, so promotion remains prohibited.
- simd-vector-reduction: Extended the exact reciprocal reducer through AArch64 NEON and VLEN-agnostic RVV butterfly outputs and inverse scaling. GCC 13.3 cross-compilation passed on the first attempt for both targets; disassembly shows NEON widening/vector reduction and RVV `vwmul`/`vnsra`/`vmerge` with no vector remainder. Prior QEMU receipts are stale after the source change, and native ARM/RISC-V performance remains mandatory.
- secret-lifecycle: Added best-effort overwrite of ML-KEM-owned secret-key slices, FO buffers/coins, candidate/implicit secrets, and provider error-path temporaries without mutating caller inputs. Added a complete ownership scenario and documented the remaining GC/compiler-copy limitation plus closure criteria in `mlkem_gc_secret_zeroization_limit_2026-08-03.md`. NFR-005 remains partial until a canonical secure owner/runtime primitive and memory-erasure evidence exist.
- contract-audit: Closed the missing REQ-001 public surface by adding `X25519MlKem768Profile` and `x25519_mlkem768_profile()` with the exact FIPS revision, TLS draft, NamedGroup, 1216/1120-byte shares, 64-byte secret, and semantic version. Added an absolute profile scenario; execution/docgen remain pending the source-matched runner.
- contract-audit: Closed missing REQ-007 type/config fields with operation, request, and verification-policy types; profile version; minimum batch; and expanded evidence for requested/selected backend, fallback, profile/fixture/source/artifact identity, compile/submit/fence/readback, and oracle status. Central config validation now rejects invalid implementation/profile versions and batches below the configured minimum. Constructors and focused scenarios were updated; execution remains pending the source-matched runner.
## 2026-08-03 — SimpleServer and Simple Browser integration

- Added negotiated NamedGroup evidence to `Tls13Context` and threaded it
  through every post-handshake context transition.
- Added the pure-Simple TLS 1.3 server application-record adapter.
- SimpleServer selects hybrid-first TLS 1.3 when `tls_min_version` is `1.3`,
  requires PKCS#8 Ed25519 material, and retains the negotiated group in its
  per-connection session.
- Browser-engine `TlsManager` now owns `os.tls13` contexts instead of browser
  TLS extern handles. Hybrid is enabled by configuration, certificate/hostname
  verification remains mandatory, `FetchEngine` loads a supported system CA
  bundle once at construction, and an empty DER trust store fails before
  network I/O.
- Added deterministic web/browser record integration coverage and its manual.
- Live hosted-renderer scheduling remains blocked: both hosted renderer paths
  still use `rt_browser_http_job_*`. They must migrate to a nonblocking
  pure-Simple job owner before browser integration is a production PASS.
- Focused check attempted once and was blocked before owned code by the
  unrelated `parser_stmts.spl` `<<<<<<< Conflict 1 of 1`; the invoked binary
  also identified itself as a Rust bootstrap seed, so it is not acceptance
  evidence.

## 2026-08-03 — Pure-Simple hybrid HRR policy

- Extended the pure-Simple HelloRetryRequest policy with NamedGroup `0x11ec`.
- Added an exact-length CH2 builder that accepts only fresh 1216-byte
  X25519MLKEM768 state and preserves the RFC 8446 synthetic transcript seed.
- The live client now rejects a server retry that selects the hybrid group
  already carried by CH1; no CH1 hybrid private material is reused in CH2.
- Added five executable SSpec scenarios and a mirrored manual for valid CH2,
  malformed length, same-group rejection, unsupported-group rejection, and one
  permitted fresh retry.
- Execution remains unclaimed because the source-matched pure-Simple runner is
  blocked and the current parser file contains another lane's conflict.

## 2026-08-03 — GPU binary audit

- Found that the CUDA checker validates a cubin but executes PTX, while the
  Metal checker creates AIR but executes a fresh source compilation.
- Production evidence aliases source/artifact/execution digests and no packaged
  X25519MLKEM768 GPU binary or keyed invalidation contract exists.
- Recorded the promotion blocker in
  `x25519mlkem768_gpu_binary_provenance_2026-08-03.md`. CUDA remains a native
  PTX-JIT arithmetic PASS only; Metal remains native-host BLOCKED.

## 2026-08-03 — SIMD backend audit

- Fixed the public batch-boundary invariant by canonicalizing arbitrary i64
  coefficients before the AVX2/NEON/RVV reciprocal reducers.
- Found process-global receipt races, inaccurate RVV chunk accounting, an MSVC
  AVX2 attribute portability gap, repeated dispatch, scalar tail layers, and
  stale current-source evidence. Recorded them in
  `x25519mlkem768_simd_backend_audit_2026-08-03.md`.
- No capped SIMD checker was rerun; all ISA promotion rows remain open.
- The updated C harness passed a focused `-fsyntax-only` gate with the required
  POSIX feature define; the first diagnostic invocation lacked that define and
  failed only at the pre-existing `clock_gettime` declaration.

## 2026-08-03 — SIMD receipt isolation repair

- Replaced the process-global ML-KEM hit counter with a saturating thread-local
  synchronous operation receipt; concurrent native threads can no longer reset
  or claim one another's SIMD evidence.
- Corrected RVV accounting to report each actual VLEN chunk.
- Added a C scenario proving a fresh thread sees zero and cannot reset the
  originating thread's receipt. The wrapper now links with pthread support.
- Updated all pinned source/probe/runner hashes. Fresh full execution remains
  deferred because this session's SIMD wrapper cap was already consumed.

## 2026-08-03 — GPU source admission hardening

- Pinned the CUDA PTX and Metal MSL source digests in their pure-Simple
  providers and fail closed on missing or changed artifacts before device I/O.
- Metal now distinguishes missing source from unavailable hardware.
- Added hardware-independent CUDA/Metal missing/digest-mismatch branches and
  updated the backend manual. Compiled-binary provenance remains open.

## 2026-08-03 — Exact GPU binary gate preparation

- CUDA now assembles and hashes a cubin for each detected device capability;
  the probe selects and loads that exact cubin per device instead of PTX.
- Metal now links and hashes a metallib in a guarded temporary directory; the
  probe loads that exact library instead of recompiling source.
- Both shell scripts and the CUDA C probe pass syntax gates. Native runs were
  not repeated, so prior PTX-JIT receipts are stale and exact-binary rows remain
  pending. Production provider packaging/loading is still open.

## 2026-08-03 — SPIR-V static diagnosis

- Arithmetic, zeta indexing, descriptors, dispatch, transfers, and emitted
  workgroup barriers are statically consistent; another blind barrier is not a
  justified fix.
- The leading hypothesis is mixed in-place shared state across divergent
  stages, with per-invocation dynamic zeta-array materialization secondary.
- Updated the Vulkan bug with serial/stage-readback localization and ping-pong
  shared-array repair criteria. No capped Vulkan execution was rerun.

## 2026-08-03 — Standards refresh and pinned-execution wave

- Refreshed primary-source research: IETF draft `-05` now marks
  X25519MLKEM768 Recommended Y after a second Last Call, but remains an active
  draft rather than a published RFC. Go defaults to group 4588 from 1.24 and
  OpenSSL 3.5 puts it first; OpenSSL also documents large-ClientHello
  middlebox/fragmentation risk.
- NIST's FIPS 203 page carries a 2025-11-17 future-correction planning note, so
  exact FIPS/profile revision binding remains release-critical.
- Parallel implementation lanes now own canonical pinned SIMD/GPU adapters,
  exact-binary GPU runner admission, and full-operation verification/allocation
  hoisting. Shared interfaces and manual step vocabulary remain those frozen in
  this state file; unavailable capability rows remain active blockers.

## 2026-08-03 — Pinned evidence reconciliation and coverage repair

- The canonical A/B/C adapter now feeds scalar, AVX2, NEON, RVV, CUDA,
  Vulkan, and Metal from one private fixture factory. Owned fixture inputs,
  returned private-key copies, decapsulation keys, shared secrets, and digest
  temporaries receive deferred best-effort cleanup; non-elidable GC erasure
  remains an explicit release blocker.
- SIMD timing now performs one untimed scalar qualification, compares every
  later timed sample to qualified public/secret digests, requires stable
  executor/artifact/RVV evidence with positive hits, and exposes no
  caller-controlled scalar-verification boolean.
- CUDA full-operation dispatch requires every operation to report the admitted
  CUBIN as its artifact and execution proof, aggregates observed lifecycle
  fields, and records the public server-share digest for both encapsulation and
  decapsulation. Vulkan exact artifact admission now precedes its capability
  blocker; Metal remains blocked by the absent retained metallib digest.
- Measured-coverage ownership is now 15 modules / 30 critical outcomes,
  including `hybrid_support.spl`. Its validator calibration passes, and the
  primary 69-local-pin manifest plus exact 11-group/36-member SSpec migration
  manifest pass their bounded shell contracts.
- The focused candidate measurement source check passed only through the Rust
  bootstrap seed. The combined five-file check reached the 55-second timeout
  without a verdict and was not retried. No native full-operation SIMD/GPU,
  measured 98% branch receipt, or promotion claim was created.

## 2026-08-03 — Pure-Simple exact GPU binding producer

- Added `src/app/test/x25519mlkem768_gpu_binding.spl`, a deterministic binding
  codec and CLI for the exact 10-field CUDA/Metal and 12-field Vulkan schema.
- Producer admission uses regular no-follow inputs, adjacent Stage-4 compiler
  provenance, manifest-pinned canonical source/binary/device tuples, before/
  after hashes, exclusive output creation by default, explicit atomic
  overwrite, and output read-back/hash verification.
- Dispatch and producer now share one canonical CUDA/Vulkan/Metal tuple
  validator. CUDA admits only the RTX A6000/sm_86 or TITAN RTX/sm_75 rows;
  Vulkan admits only the paired retained SPIR-V set before its runtime
  capability blocker; Metal remains blocked without a retained metallib hash.
- Added behavioral codec SSpec coverage and registered it as member 37 in the
  11-group SSpec family manifest. The bounded two-file source check reached its
  55-second timeout without a verdict and was not retried.

## 2026-08-03 — Stage-4 tag-18 diagnostic advance

- Reused the later sanity-passing pure-Simple Stage-3 candidate for one strict,
  diagnostic-only full-CLI build; its missing canonical provenance prevents any
  product or crypto-evidence claim.
- The fixed 240-second run converted 1,006 module surfaces and emitted no
  parser error, OOB, fallback, crash, or recurrence of the former EXPR_BLOCK
  tag-18 failure in `main_and_help.spl`.
- The run ended only at its timeout while still in Phase 2. The retained log is
  `build/mini_builds/x25519mlkem768-stage4-after-block.log`; admitted Stage-4
  compiler provenance and downstream native X25519 evidence remain open.

## 2026-08-03 — Adjacent spawn frontend hardening

- Added the missing flat `EXPR_SPAWN` conversion instead of silently returning
  NilLit, then extended async desugaring across common statement/value and
  recursively nested expression positions.
- Aligned E1049 transfer/share checking with the real desugared `spawn_actor`
  HIR callee while retaining legacy `spawn` recognition.
- Expanded behavioral coverage for direct, constructor, full-frontend, nested
  initializer, loud-fallback, and safety-boundary cases. Three bounded
  seed-backed checks timed out without diagnostics or verdicts; admitted
  self-host execution remains required.

## 2026-08-03 — Canonical Phase-4 cycle-1 result

- The external canonical build produced admitted Stage-3 provenance, passed
  the former EXPR_BLOCK parse point, and reached Phase 3.
- It then failed deterministically because the compiler lint model and shared
  EasyFix payload supplied conflicting same-named `LintLevel`/`LintCategory`
  identities.
- Removed the duplicate compiler enums and re-exported the canonical shared
  payload types; the focused behavioral identity spec passed 1/1 under the
  Rust seed as development evidence. The repair is recorded in
  `stage4_lint_payload_enum_identity_conflict_2026-08-03.md` and awaits the next
  bounded Stage-4 cycle.

## 2026-08-03 — Hybrid support behavioral coverage

- Added a modern executable SSpec for shared byte/digest/comparison support
  behavior, including observable best-effort list/byte-array clearing and a
  known SHA-256 oracle. This is not non-elidable erasure or all-branch evidence.
  Empty locals and byte arrays are explicitly typed where inference is not
  sufficient.
- Reused the execution-policy injected-ISA seam so fail-closed provenance can
  be tested without linking or executing a SIMD intrinsic; no test-only API is
  exported from the production hybrid-support owner.
- The focused Rust-seed development run passed 8/8 examples. The primary
  manifest passes with 73 local pins, and the planning-only dynamic-family
  manifest passes at 11 groups / 38 members. No measured coverage or admitted
  self-host claim is made.

## 2026-08-03 — Support review and adjacent compiler repairs

- Independent review removed the injected-ISA test API from production,
  corrected wipe/constant-work overclaims, added fail-closed slice bounds, and
  repaired the critical-owner hash cascade. The focused support spec passed
  8/8 and branch-receipt calibration passed; both are seed/development gates.
- Primary/family manifests were mechanically repinned after that final cascade
  but were not executed a fourth time because the three-cycle guard was
  reached. Their last executed results preceded the final coverage hash update.
- Added missing flat-bridge Await/Yield mappings and recursive yielded-expression
  desugaring. The focused frontend spec passed 9/9 under the seed.
- Stage4 forensics found the running pre-repair snapshot effectively serial
  with severe heap growth. HIR scratch was allocated after the transient scope
  pause; the worktree now lowers while scoped and atomically promotes HIR,
  diagnostics, retained traits, bootstrap functions, and all bootstrap module
  roots before reclaim. An earlier seven-scenario source-order shape passed
  under the seed; the final carrier/reset-delta shape was not rerun after the
  three-cycle cap and is not runtime ownership evidence.

## 2026-08-03 — Independent full-oracle receipts and Stage4 retry audit

- Retained fresh offline Go 1.24.0 and CIRCL v1.6.4 raw logs, exit-code files,
  and a receipt under
  `build/evidence/x25519mlkem768/oracle-full-20260803/`. Both independently
  passed complete comparison sets A (ML-KEM), B (RFC 7748 X25519), and C
  (draft-05 hybrid composition). This proves exactly two current full
  comparators; the manifest promotion rule still requires a source-matched
  admitted pure-Simple native third result.
- Corrected the full pure-Simple oracle probe's empty-list local to explicit
  `list` typing and repinned the oracle, primary, and family manifest identity
  cascade. Capped manifest contracts were not rerun.
- The external retry uses stale git snapshot `4505aec902a7...`, has no Stage4
  artifact, and lacks the current arena preparation and retained-root repair.
  Prior attempts ended at HIR 32, 224, and 448 with roughly 1.95, 10.75, and
  24.09 GiB RSS. The live retry remained at 32/1,431, exceeded 3.5 GiB, and
  added about 2.8 million registry objects in one module. It cannot qualify the
  current compiler, validate bounded memory, or admit the pure-Simple oracle.
- The 448-module attempt terminated on `unresolved type: int` in lint
  `_brace_delta`. Replacing its inferred character iterator with explicitly
  typed `i64` index/delta and `text` character locals passed the focused 1/1
  seed source contract; the failure and admission rule are recorded in
  `stage4_lint_brace_delta_unresolved_int_2026-08-03.md`.

## 2026-08-03 — Live web integration, quarantine ownership, and SSpec cleanup

- Added a real loopback Simple Browser to production SimpleServer integration
  scenario using the host-stream TLS transport, mandatory X25519MLKEM768,
  explicit test-only Ed25519 trust, an encrypted HTTP GET, and deterministic
  worker shutdown. The existing five adapter scenarios passed; the live sixth
  scenario failed closed before handshake because the selected Rust bootstrap
  seed cannot provide `rt_entropy_fill`. This is not a network/TLS pass and
  requires the source-matched admitted native runtime.
- Bound the test-only localhost certificate, private key, response body, and
  live spec hashes in the primary evidence manifest. They are never production
  trust anchors.
- Metal and Vulkan now terminalize executors on unknown completion. Accelerator
  cache invalidation, replacement, and shutdown clean typed owners before
  metadata removal and retain the final strong owner when cleanup is unknown.
  The cache closes with `x25519mlkem768-cache-gpu-cleanup-pending`; no backend
  currently proves a quarantined unknown-completion session safe to reap, so a
  process-lifetime safe leak remains preferable to reuse or use-after-free.
- Hoisted AVX2/NEON/RVV selection out of the ML-KEM per-chunk butterfly loop,
  retained exact hit accounting and scalar tails, and added a modern SIMD
  structural SSpec/manual. Its one structural seed run and C syntax gate pass,
  but all prior physical SIMD correctness/performance receipts are stale for
  the changed runtime source.
- Migrated legacy `expect_not` calls and non-inferable empty-list locals across
  the X25519MLKEM768 specs to built-in boolean matchers and explicit `list`
  types. Registered the SIMD spec as family member 39. A read-only hash-graph
  audit passes for 79 identities, 11 groups, and 39 members; the capped primary
  and family execution contracts were not rerun.

## 2026-08-03 — Coverage expansion, Vulkan recovery, and perf identity

- Expanded the measured-coverage contract from 15 owners / 30 outcomes to 23
  owners / 112 paired outcomes across scalar hybrid operations, native SIMD,
  CUDA/Metal/Vulkan sessions and providers, browser TLS/HTTP, and server TLS
  configuration/worker behavior. The 11-workload producer and all outcome rows
  remain deliberately unmeasured until a source-matched pure-Simple full CLI is
  available; static consistency is not a coverage percentage.
- Vulkan unknown-completion ownership now transfers exact dependencies to the
  existing SFFI quarantine. A one-pass recovery waits for device idle under the
  SFFI lock before reaping and retains failed owners. CUDA remains unsupported
  because no current-context query/restore API exists; Metal remains unsupported
  because no command-buffer handle/status/wait owner is retained. These are
  explicit observable blockers, not silent cleanup successes.
- The full-operation performance validator now requires every SIMD/GPU row to
  share the scalar row's fixture, batch map, sample count, and warmup count, and
  requires positive ordered scalar p50/p95/p99 values before accepting speedup.
  No specialized physical receipt has been promoted after this contract change.
- The live web scenario now derives a process-local loopback port and validates
  worker creation before connecting. Its source-matched execution still awaits
  the admitted runtime entropy surface.
- Reconciled the final evidence hash dependency graph after the parallel lanes:
  the primary manifest is `e59560f7df164929c2256d78bfa9facd438d7f293c33e7a47e9ac25edea20d34`.
  The family manifest now has 11 groups / 41 members and is planning-only until its
  exact source snapshot is compiled and executed.

## 2026-08-03 — Branch-contract audit and hash repair

- Added behavioral production-boundary SSpec for AVX2/NEON/RVV operation
  receipts: zero-hit, unknown/mismatched backend, RVV VLEN boundaries,
  non-RVV metadata rejection, and successful evidence promotion. Added a
  second behavioral SSpec for exact GPU scalar verification, five independent
  corrupted outputs, and all three checked ML-KEM dependency errors. These
  scenarios are authored and mirrored in manuals but remain unexecuted under
  the exhausted three-cycle Stage4 cap.
- Added duplicate Stage4 `source_roots` rejection, Vulkan zero-batch policy
  rejection, and the empty byte-append edge. No production test-only seam was
  introduced.
- Repaired stale critical anchors and added the two new Vulkan
  `release_pending` condition outcomes. The inventory is now 23 owners / 56
  logical conditions / 112 outcomes. The canonical symbolic hash is
  `5da7a50d0b5f13d0416968eb1c491fd17eebf07d418bc069cdb8d2dbc8a50a64`;
  the coverage schema hash is
  `bceed0374be362c75bd7d1cf471a4f6a2ea45709fadd656b3676fa894376eaf0`;
  the primary manifest hash is
  `e59560f7df164929c2256d78bfa9facd438d7f293c33e7a47e9ac25edea20d34`;
  and the family manifest hash is
  `7013fb06b58cae2847d7bbf6acf42fad96e3666579dbd35397bf00d730e88a99`.
- Audit blockers remain explicit: native C SIMD lacks measured coverage
  probes, coverage is aggregate rather than per-owner, retained SIMD receipts
  are stale or missing, runner AOT provenance is not bound to operation
  evidence, matrix receipts are synthetic-only, and performance calibration
  records do not recompute raw samples or force observed scalar execution.
- Scoped static verification exhausted its three-cycle cap. Anchor/hash/stub/
  layout checks passed and the family contract reached the exact 41-member
  list, then failed because its later member-pin and final status literals still
  said 38. Both literals are now 41, but no fourth retry was run; the family
  contract remains unverified rather than promoted to PASS.

## 2026-08-03 — Scalar performance observation hardening

- Claimed the false-green where the scalar performance SSpec used the
  `Automatic` plus `Suggest` default. Its cold and sampled full-operation paths
  now share an explicit `ScalarCpu` plus `Require` configuration.
- Added a pure observation validator to the retained evidence runner. Before a
  scalar receipt is labeled, keygen, encapsulation, and decapsulation must bind
  the expected operation, scalar requested/selected backend, common valid
  configuration digest, input/output proof, `pure-simple-scalar` executor, no
  fallback, and zero SIMD/GPU lifecycle state. The typed integration SSpec adds
  exact success plus wrong-backend, operation, proof, fallback, lifecycle, and
  default-policy mutations.
- This prevents scalar mislabeling but does not close NFR-011. No retained raw
  30-sample/two-warmup artifact, RSS, host/clock/session binding, or recomputed
  promotable performance receipt was produced. The family/Stage4 verification
  cycle remains exhausted and was not rerun.
- Updated primary manifest hash:
  `e59560f7df164929c2256d78bfa9facd438d7f293c33e7a47e9ac25edea20d34`;
  updated 41-member family manifest hash:
  `7013fb06b58cae2847d7bbf6acf42fad96e3666579dbd35397bf00d730e88a99`.

## 2026-08-03 — Final Stage4 cycle and qualified-type repair

- Retained cycle-2 evidence under
  `build/evidence/x25519mlkem768/stage4-current-cycle2-20260803/`. It reached
  512/1,442 HIR modules and failed on the parser-supported qualified payload
  type `std.common.color.types.Color`; the run was not OOM.
- Fixed the pure-Simple HIR owner instead of rewriting valid source. Qualified
  type names now resolve the exact module surface and retain their full lookup
  key. Exact imported-enum/collision-order and adjacent direct-signature
  regression scenarios were added to the HIR import-resolution SSpec/manual.
- The third and final capped build passed the exact prior module:
  `web_render_backend` reached `phase3:hir:file:done` without the `Color`
  diagnostic. Evidence is retained under
  `build/evidence/x25519mlkem768/stage4-current-cycle3-20260803/`; Stage4 log
  SHA-256 is `8b03bfa925dae489952cb1514c93205f9f01ca29ddbd1b774ef6f951c8419f28`.
- Cycle 3 then failed later at the existing fail-closed #158 Phase-B gate:
  `Future<T>.map<U>` and `Future<T>.then<U>` cannot reach native code until
  real monomorphization is implemented. The authoritative design is
  `doc/03_plan/compiler/generics/native_monomorphization_plan_2026-07-17.md`;
  whitelisting or erasing these value-transforming methods is rejected because
  it can silently miscompile payloads.
- The three-cycle guard is exhausted. A fresh session must implement and prove
  #158 Phase B, then resume with
  `CAP_MEM_MAX=32G scripts/resource/run_capped.shs sh scripts/bootstrap/bootstrap-from-scratch.sh --full-bootstrap --mode=one-binary --full-cli --jobs=full --output=build/x25519-stage4-current --progress=<new-log> --progress-interval=15`.
  Owner: compiler monomorphization lane. Merge owner and final reviewer: normal
  highest-capability Codex. Until that succeeds, the source-matched pure-Simple
  third oracle, fresh coverage receipt, SIMD measurements, and GPU execution
  rows remain active and unaccepted.

## 2026-08-03 — Dead entry-closure dependency removed

- Parallel analysis proved `Future<T>.map<U>` and `then<U>` were import/module
  reachable but not call reachable from the CLI. Database feature/test modules
  had unused bare `use std.io` imports; that facade pulled async traits and the
  Future family into the executable closure.
- Removed the dead import from all four sync/async database family files. Added
  a modern SSpec/manual that parses imports through the canonical compiler
  scanner, retains concrete database owners, rejects `std.io`, and proves the
  #158 safety gate was not weakened with a `map`/`then` whitelist.
- This is also a Stage4 performance correction: the previous cycle spent work
  lowering declarations that the CLI cannot call. The fresh module count and
  elapsed/RSS delta remain unmeasured because the three-cycle guard forbids
  another bootstrap in this session.
- General owner-aware monomorphization remains incomplete and is not claimed:
  MethodCall/StaticCall lose generic arguments, the current Phase-4 pass is a
  no-op, and declaration/type closure is still conflated with executable-body
  closure. These remain explicit compiler work rather than an X255-specific
  unsafe bypass.

## 2026-08-03 — Independent pinned Set A/B/C receipts

- Replaced the literal `set_a_passed`, `set_b_passed`, and `set_c_passed`
  fields with typed v3 Set A/B/C receipts. The finalizer now checks fixed
  lengths before slicing, validates ML-KEM, X25519, and hybrid public outputs
  and both secret sides independently, and constructs receipts only on exact
  oracle and round-trip success.
- Corrected the false `public_output_bytes=2400` label. The retained receipt
  now distinguishes 2336 public-wire bytes from 2400 total observed bytes.
- Secret-derived digests remain internal. Owned ML-KEM and X25519 secret slices
  are wiped through deferred cleanup and never enter the public receipt.
- Added three modern focused SSpec groups for exact receipts and adjacent
  identity, boundary-length, digest, secret-oracle, recovered-secret, and
  round-trip failures. CUDA dispatch now treats successful typed receipt
  construction as the A/B/C correctness proof.
- The canonical runtime wrapper rejected the deployed executable as
  non-production before checking source. No seed fallback or fourth Stage4
  cycle was used; this change is authored and statically audited, not promoted
  to runtime PASS.
- Current primary manifest SHA-256:
  `58f711297f346e7883e47cfb7b1cb7047c11d20aa7fedce90e9fc176422b7a9d`.
  Current 41-member family manifest SHA-256:
  `99e92e78d651fa49c7546cb8a7825dff4836fda05bf01e72a9f5bb6624501d12`.

## 2026-08-03 — Vulkan exact-SPIR-V pinned-fixture caller

- Added the first direct caller of the shared pinned Vulkan workload. It uses
  the exact retained forward/inverse SPIR-V paths and digests, one persistent
  executor, and the same `Require + AbsoluteAndScalar + batch_size=1` config
  as the other pinned backends.
- On a capable host the scenario requires typed Set A/B/C receipts, seven
  kernel invocations across three accelerated operations, exact artifact-set
  provenance, scalar-oracle agreement, no fallback, complete lifecycle, and a
  single session generation. Missing artifacts and unavailable Vulkan remain
  explicit blockers and cannot create output evidence.
- Production Vulkan dispatch remains blocked pending runtime API/device tuple
  binding. Metal remains blocked pending a retained and manifest-pinned
  metallib; source JIT is not accepted as binary evidence.
- The canonical wrapper still refuses the deployed non-production runtime, so
  this caller is authored but has no new physical/runtime PASS. Current family
  manifest SHA-256:
  `16ab2bc08d61a3986c4905396d85b2b39862374f54094cc4c4bda27b67617513`.

## 2026-08-03 — Vulkan zeta serialization cache

- Moved serialization of the public ML-KEM zeta table from every Vulkan NTT
  dispatch to persistent-executor construction. A full seven-dispatch pinned
  exchange now reuses one 512-byte encoding; the native caller requires the
  retained encoding count to remain exactly one.
- Repaired the changed critical-owner hash and terminal-session line anchors.
  Scoped structural, symbolic, schema, manifest, and family pin checks passed.
  Current hashes: critical symbolic
  `884da30085f74ac60ab41f14c5238b40d5414b377eb29c73c66606193c3b4954`,
  coverage schema
  `f3bf12c358d9051888b64a6e1bfedf65622030d5e8cc47572a3aa56e9204578f`,
  primary manifest
  `26f7efbdc88aab30cfc9b3720d3ffb368e0f57506a4ba72fd3a72e11a6e3d248`,
  and family manifest
  `5b5c8b602c4d48e9e78bb7a28915d3d266a63fc8d94a44f6fa5905b1779c288b`.
- This removes repeated CPU/allocation work but does not supply measured
  speedup evidence; runtime remains unavailable under the production wrapper.

## 2026-08-03 — Vulkan latest-operation fence truthfulness

- Vulkan now clears `fence_completed` at the start of each non-closed operation
  attempt. The physical pinned scenario follows a successful exchange with an
  empty batch and requires the exact input error plus a false fence state.
- Scoped lifecycle, critical-owner anchor, symbolic, schema, and manifest pin
  checks passed. Current hashes: critical symbolic
  `2597ec804f4c232d5a97fdbf1370fcbec07f32c92fb19bfb85b4292d66eca9d8`,
  coverage schema
  `145a24c78779dbc76931d402312e1e2e82bf16a25987cfc2815461f1ea021501`,
  primary manifest
  `894b26e7076b4f211fae502d377c2182ea4aeab054853f29e22f78da8f6181fc`,
  and family manifest
  `d3cf32d30ffdd48a5ed8c736d06a5321e24c10988d7ea195ac21849016e3cf47`.
- Runtime execution is still unverified under the rejected non-production
  deployed binary.

## 2026-08-03 — Vulkan facade batch-scope correction

- Corrected the integration config from `batch_size=3` to `batch_size=1`.
  Each facade call performs one handshake operation; provider polynomial
  batching is not relabeled as multiple handshakes. Outer retained-executor
  runners remain responsible for real repeated-handshake counts.
- Zero-safe static config and family-pin checks passed. Current family manifest
  SHA-256:
  `d3cf32d30ffdd48a5ed8c736d06a5321e24c10988d7ea195ac21849016e3cf47`.

## 2026-08-03 — Backend matrix receipt v2

- Replaced first-blocker admission with a canonical seven-row scan that retains
  simultaneous blockers, failures, and public-output mismatches. Each row now
  binds a validated admission phase, source/admission reasons, host and artifact
  provenance, and typed public Set A/B/C receipts.
- Added a fail-closed executed-row composer and modern branch scenarios for
  phase claim smuggling, canonical-oracle fabrication, runner/artifact drift,
  host/ISA proof, GPU lifecycle, output mismatch, failure retention, scalar
  propagation, receipt injection, permutation, and duplicate/missing rows.
- Public receipt SHA-256:
  `dff5204613066eee498d00643d79dd50bbbe4f284aa10cf630491da84f0f3625`.
  Matrix owner SHA-256:
  `49781142b3ab8205f812689e5cac762a79f2aa76468cf9bc8978a737c7ccec5d`.
  Composer SHA-256:
  `2cc705c95e7ad9bc698a371821cf8495f99393c6acd51b7695decfdea4afe290`.
  Matrix SSpec SHA-256:
  `3aae5b9ae64373428da28b9e4aa27bc0f4bfc0c633f9b47203daa56e2c95f928`.
  Primary manifest SHA-256:
  `518e6efd590f9d264dc0be003b8d71a3591f4eadda24a9613d0ac2a14c60dfe2`.
  Family manifest SHA-256:
  `48769c3aa858673ad0b428e911bba418dbca0cb951f0564c8712dee0a18bf95f`.
- Status: authored and statically reviewed only. The rewritten scenarios are
  synthetic branch fixtures, not promotion evidence, and remain unexecuted by
  an admitted self-hosted runtime.

## 2026-08-03 — Matrix-qualified raw performance timing

- Added `qualified_timing.spl` with role-fixed scalar/candidate warm receipts,
  ordered 30..1024-sample receipts, canonical sample hashing, internally
  derived p50/p95/p99 and throughput, exact full-exchange/hybrid-operation
  counts, and contamination rejection.
- Performance attestation schema v5 now consumes admitted raw timing for both
  roles plus paired schedule v1 and binds the pair digest. AVX2 downstream
  admission carries the same qualified-timing identity.
- CUDA/Vulkan/Metal timing admission requires per-exchange transfer, launch,
  synchronization, and device-readback counts. AVX2/NEON/RVV require full
  accelerated-operation coverage; RVV also requires observed VLEN.
- Hardened qualification revalidation after canonical rehash. It now rejects
  wrong version/profile/target/source identity and noncanonical public Set
  A/B/C receipts rather than treating a recomputable hash as authority.
- Fixed candidate batch private-input aliasing by giving each keygen an owned
  `[u8]` copy, wiped all live secrets on digest failure, and retained ordered
  sample hash plus 1-exchange/3-operation counts.
- Corrected the scalar performance wrapper identity from
  `Automatic + Suggest` to executed `ScalarCpu + Require`; its contract checks
  the exact configuration digest while retaining the compatible v2 envelope.
- `runtime_need`: none. `facade_checked`: existing qualified crypto/timing and
  time facades. `chosen_path`: `reuse-facade`.
  `rejected_shortcuts`: raw runtime timing/process aliases, unqualified SIMD
  entrypoints, caller-only aggregate metrics, secret-derived evidence hashes,
  and synthetic physical-performance promotion.
- Runtime status remains unverified because the canonical self-hosted runtime
  is unavailable/non-production. New unit fixtures prove contract branches,
  not physical CPU/GPU performance. Manifest and critical-coverage hashes are
  intentionally pending until the v5 interface is statically clean.

## 2026-08-03 — Timing collector trust-boundary hardening

- Measurement qualification schema v2 binds scalar and candidate backend
  artifacts, configurations, and executor identities and rejects rehashed
  Set A/B/C permutations.
- The SIMD raw batch and composer are now private. The sole public collection
  function measures the batch, obtains Linux process `VmHWM` itself, and fails
  closed instead of accepting caller-supplied samples or RSS.
- The owned private-input copy is prepared before the timed interval; warmup
  accounting records one scalar differential qualification plus two candidate
  warmups as three completed exchanges.
- Throughput now counts the receipt's three hybrid operations per exchange;
  invalid sample sets return zero from public aggregate helpers instead of
  indexing or dividing unsafely.
- Raw timing admission bounds sample count before canonical receipt hashing,
  scalar/candidate performance sample counts must match, and performance
  measurements must exactly match all overlapping raw-timing identity fields.
- Remaining authenticity gap: SHA-256 receipts are consistency/integrity
  evidence, not proof that a protected collector produced them. Physical
  promotion still requires a pinned, prebuilt collector or COSE/Ed25519 signer
  with a key unavailable to ordinary callers.
- Remaining portability/trust gaps: live host/architecture/session/clock are
  not observed independently and peak RSS is Linux-only. Paired schedule v1
  now defines retained interleaving, but the candidate-only collector cannot
  produce it. These are release blockers, and candidate success/error branches
  still require physical backend-host coverage.
- Perf bug found: `time_now_nanos()` differs across runtime lanes in clock
  source and epoch semantics. Same-process deltas are usable, but a generic
  clock label cannot authorize cross-receipt comparison. The required next
  owner is a platform measurement observer that binds OS/arch, exact clock
  domain, CSPRNG session nonce, and typed peak memory into all receipts.
- Added the neutral pure-Simple `platform-measurement-observation-v1` contract,
  near-complete branch spec, and manual. It distinguishes process peak RSS from
  SimpleOS guest heap high-water and has no runtime/env/process I/O. The
  platform-owned producer and receipt integration remain pending.

## 2026-08-03 — Paired benchmark schedule v1 and attestation v5

- Paired schedule v1 binds an even count in 30..1024 of zero-based ordinals to
  scalar and candidate
  monotonic start/finish intervals and the exact ordered timed-receipt samples.
- Even ordinals require scalar then candidate; odd ordinals reverse the order,
  forming ABBA across adjacent pairs. Admission rejects wrong durations,
  within-pair order violations, cross-pair overlap, and qualification,
  session, clock, or timed-receipt rebinding.
- The role-fixed qualified-timing digest includes the admitted schedule receipt
  hash, and performance attestation schema v5 requires that schedule before
  threshold admission.
- The current SIMD collector remains candidate-only and cannot emit the scalar
  half of the schedule. No new physical x86/ARM/RISC-V SIMD or
  CUDA/Vulkan/Metal performance PASS is claimed; those rows remain blocked
  pending a trusted paired collector and platform observer.

## 2026-08-04 — Seed reports SIMD backend 0 by design; collector unblock is not verifiable on the default toolchain

- Ran the paired-collector unblock as the next step and stopped before landing
  it, because the premise it rests on does not hold on the default toolchain.
- `x25519_mlkem768_measure_simd_paired_timing` is blocked by a single early
  `return Err("X25519MLKEM768 trusted same-owner SIMD timing unavailable")` at
  `src/app/test/x25519mlkem768_candidate_batch_measurement.spl:503`. The full
  real implementation already sits beneath it as dead code (`_qualify_oracle`,
  two `_fresh_exchange` warm-ups, `_collect_paired_samples`, the schedule build
  and all four admission calls). Removing that one line activates written code,
  not a stub. The stated fix — moving the ABBA loop behind one same-owner
  differential-oracle entry point in `src/os/crypto/x25519_mlkem768/hybrid.spl`
  so `verify_scalar: false` never has to be exported — remains correct.
- **The blocker underneath it: `mlkem_ntt_simd_backend()` returns 0 on every
  runtime reachable from `bin/simple`, and that is deliberate, not a defect.**
  `src/compiler_rust/compiler/src/interpreter_extern/simd.rs:133` implements the
  `rt_mlkem_ntt_simd_backend` extern in Rust as a hardcoded `Value::Int(0)`,
  with the comment: "The ML-KEM candidate is admitted only from the compiled C
  runtime. Returning backend=0 keeps interpreter/seed runs honest: they exercise
  the scalar fallback but cannot manufacture a native execution receipt."
- Measured, not assumed:
  - Host is x86_64 with `avx2` in `/proc/cpuinfo`.
  - The C ground truth says AVX2 is present: compiling `runtime_simd_dispatch.h`
    directly and calling `simd_detect_avx2()` prints `C_simd_detect_avx2=1`.
    `SIMD_CAN_AVX2` is unconditionally 1 on x86_64, so the C path is not gated
    out at compile time.
  - A Simple probe with a live control value prints `CONTROL 42` then
    `BACKEND 0` and `RECEIPT_BACKEND 0` — under JIT **and** under
    `SIMPLE_EXECUTION_MODE=interpret`, and on `bin/simple_seed`. So this is not
    the known JIT-only unregistered-extern nil trap; every reachable mode
    answers 0.
  - The deployed `bin/simple` probes as the Rust seed
    (`strings | grep -c "enum construction: unregistered enum"` = 0), which is
    why the Rust stub is the implementation that answers.
- Consequence for this campaign: with backend 0, the candidate branch fails
  admission before doing any work, so removing the `:503` guard cannot yield a
  SIMD measurement through `bin/simple run`/`test`. Any spec asserting a SIMD
  paired PASS on the default toolchain would be **vacuous by construction** —
  the same false-green shape this campaign has already been bitten by.
- The real measurement lane is a natively-compiled binary linked against
  `runtime_simd_dispatch.o`. `build/check/x25519mlkem768-cpu-simd/` is that
  lane; its checked-in artifact is a **riscv64** build whose `output.txt`
  records a genuine `mlkem_ntt_simd_backend=3`, RVV VLEN 256, 1056 hits,
  `MLKEM_NTT_SIMD_C_TEST: PASS`. The sibling `x86/` directory is **empty** — the
  x86 native lane has never been built here, and the stale riscv64 binary will
  not run (missing `/lib/ld-linux-riscv64-lp64d.so.1`).
- Next step, in order: build the x86 native SIMD lane so `backend=1` is
  reachable on this host; only then land the same-owner paired entry point and
  the `:503` removal, and verify the ABBA span ordering against a runtime that
  can actually execute the candidate. Landing the crypto change first would be
  an unrunnable edit.
- Still no physical x86/ARM/RISC-V SIMD or CUDA/Vulkan/Metal performance PASS is
  claimed. Correction to the prior entry's framing: the collector is not merely
  "candidate-only" — on the default toolchain there is no candidate backend at
  all.
- Also corrected: there is no family of per-backend SIMD collectors. There is
  one SIMD collector plus one backend-neutral GPU collector
  (`src/app/test/x25519mlkem768_gpu_paired_measurement.spl`), which returns a
  blocked *value* rather than `Err` and is gated on a different root cause
  (no trusted live-executor lifecycle snapshots).

## 2026-08-04 — x86 native CPU-SIMD lane built and PASSING on this host (backend=1)

- Built the previously-empty x86 half of the native lane by running the
  repo's own producer, `scripts/check/check-x25519mlkem768-cpu-simd.shs`
  (exit 0). This closes the gap noted in the entry above: the `x86/` directory
  is no longer empty, and `backend=1` is now reachable on this machine.
- Receipt, measured this run (not asserted from the seed):
  - `mlkem_ntt_simd_backend=1` — AVX2, matching the C ground truth
    (`C_simd_detect_avx2=1`) and contradicting the seed's designed 0.
  - `mlkem_ntt_avx2_reduction_mismatches=0`
  - `mlkem_ntt_simd_forward_hits=240`, `mlkem_ntt_simd_total_hits=480` — real
    native SIMD execution, not a scalar fallback.
  - `mlkem_ntt_simd_thread_local_receipt=pass`, `MLKEM_NTT_SIMD_C_TEST: PASS`
  - `mlkem_cpu_simd_execution_class=native`, `mlkem_cpu_simd_status=pass`
  - `mlkem_cpu_simd_curve25519_smalllimb_dependency=absent`
  - Pinned digests: checker
    `2b63ff26e6b44d462db9c0dfaca462ee42ba85f31187c4de38bac5b3366c1662`,
    runtime source
    `98a1b781b01c26a30a6100fb08d9c8f06ce6eda8030df244088cdb5c6768f053`,
    binary
    `837d6bded0aa64ab8d3913cbce913d9234d737eb4064bcb3ee6edbe810aa1133`.
- **Scope of what this does and does not prove.** The lane itself reports
  `mlkem_cpu_simd_evidence_scope=correctness-only`,
  `mlkem_cpu_simd_performance_status=not-run`, and
  `mlkem_cpu_simd_promotion_status=not-proven`. So this is a genuine native
  AVX2 **correctness** receipt on x86, and nothing more — it is **not** a
  paired timing measurement and **not** a performance PASS. No speedup or
  threshold claim is made.
- What it changes for the campaign: the "no reachable SIMD backend" obstacle is
  now specific rather than absolute. Native x86 AVX2 execution is demonstrably
  available through the C-runtime lane, while `bin/simple` still reports 0 by
  design. The paired collector still cannot be verified through `bin/simple`;
  it needs to run in this native execution class.
- Unchanged next step, now better grounded: land the same-owner paired
  differential-oracle entry point and the `:503` removal, and verify the ABBA
  span ordering in the **native** lane above rather than on the seed. Still no
  physical SIMD or GPU performance PASS is claimed.

## 2026-08-04 — parse blocker cleared, campaign source landed, SIMD path measured

### Landed on main

- `e6217b01475` — campaign source (92 files, all additions) plus two modules the
  campaign imports that existed only in a jj working-copy snapshot:
  `src/lib/common/platform_measurement_observation.spl` and
  `src/lib/common/encoding/sha256_contract.spl`. Their absence made importing
  specs fail at an *unrelated* call site: an unresolved `use` is only a WARN, so
  one missing leaf poisoned the graph and surfaced as `function ... not found`
  somewhere else entirely.
- `d8a8fbc5164` — `X25519_MLKEM768_PINNED_SERVER_X25519_SHA256` was **63 hex
  chars**, the trailing `4` dropped. `_executed_row_hex64` rejects any value
  whose `len() != 64`, so Set B failed on every call and returned before Set C
  could run. Value recovered by reproducing the sibling constant exactly:
  `sha256(RFC 7748 Alice pubkey)` = `300c9c96...d63425ae` matches the in-repo
  client constant bit for bit. Derived, not hand-entered.

### Measured verdicts (`SIMPLE_TIMEOUT_SECONDS=0` on every run)

| spec | verdict |
|---|---|
| `x25519mlkem768_avx2_full_operation_receipt_spec` | `4 total, 4 passed, 0 failed` |
| `x25519mlkem768_evidence_contract_spec` | `11 total, 11 passed, 0 failed` |
| `x25519mlkem768_executed_row_composer_spec` | `8 total, 8 passed, 0 failed` |
| `x25519mlkem768_pinned_workload_spec` | `8 total, 8 passed, 0 failed` (uncommitted tree) |
| `x25519mlkem768_simd_operation_evidence_spec` | `4 total, 4 passed, 0 failed` (uncommitted tree) |
| `matrix_receipt`, `measurement_qualification`, `performance_attestation`, `qualified_timing` | **TIMEOUT, no `Results:` line** |

Timeouts are recorded as timeouts. They are not passes and not failures.

### The SIMD backend question, resolved against the earlier finding

The prior note "seed returns SIMD backend 0 by design — Rust stub" is **too
broad**. Verified at source: `simple_runtime::value::simd_int_ops::mul_i32x8`
uses `_mm256_loadu_si256` / `_mm256_mullo_epi32` / `_mm256_storeu_si256` behind a
runtime `is_x86_feature_detected!("avx2")` guard, with a scalar fallback — 57
such intrinsic uses in that file. So `std.simd`'s integer vector ops are **real
AVX2**, and a Simple-level kernel built on them genuinely executes AVX2. The
"stub" characterisation applies to the ML-KEM NTT batch hook, not to the vector
ops.

`mlkem_ntt_simd_backend()` means **"is the native SIMD NTT batch path usable"**,
not "does this CPU have a vector unit". Consumers pin this:
`execution_policy.spl:111-117` tests `native_backend == 1/2/3` and `:136` emits
"requested SIMD candidate is unavailable on this host". Reporting CPU capability
there is wrong twice over — it fabricates the recorded backend, and it opens the
gate at `ml_kem_ntt.spl:223/298` onto `mlkem_ntt_simd_batch`.

### Uncommitted, verified but not landed

- `src/lib/nogc_sync_mut/simd.spl` — `MlKemNttSimdReceipt`,
  `mlkem_ntt_simd_backend/reset/receipt/batch`, the last being an AVX2 NTT batch
  kernel (five butterfly layers at stride >= 8 through `simd_mul_i32x8` /
  `simd_add_i32x8` / `simd_sub_i32x8`; stride-4 and stride-2 layers stay scalar
  and are not counted as chunks).
- `src/os/crypto/ml_kem.spl`, `ml_kem_kpke.spl`, `ml_kem_ntt.spl` — the nine
  `ml_kem_*_checked*` functions, `trait MlKemNttBatchProvider`, `ntt_simd` /
  `intt_simd`. Implicit rejection preserved constant-time via
  `_ct_select_bytes(_ct_bytes_eq(c, c_prime), k_prime, k_implicit)`
  (`ml_kem.spl:380-381`, `:517-518`); no secret-dependent early return.
- `test/fixtures/crypto/x25519mlkem768/` — 25 files, restored at the **newest**
  blob per path (`manifest.sdn` has 43 revisions, `sspec_family_migration_manifest.sdn`
  39; picking an arbitrary commit would install stale content that looks fine).

**These 731 added lines across three key-generation files are NEW work, not
recovered loss.** `1c74085cfce` is not an ancestor of `main`. Checked directly:
`ml_kem.spl` was 335 lines at `118c636ead8^` (before the wipe), 0 during it, and
335 at `7f5a55fa46e` (the revert) and on main today — the revert was **complete**.
`ml_kem_keygen_checked` has zero definitions at every point in main's history.
Treat this as new crypto needing review, not as a repair.

### What the 8/8 does and does not prove

During that run `mlkem_ntt_simd_backend()` returned **1** and both source files
were frozen beforehand (`simd.spl` 12:54:45, `ml_kem_ntt.spl` 12:35:24; run
12:56:30-13:09:38). So the gate was open and the AVX2 kernel really executed on
the keygen path, and the spec checks outputs against pinned SHA-256 constants —
a wrong NTT would break those digests. That is genuine bit-correctness evidence
for one workload.

**Superseded as vacuous:** an earlier `keygen_driver` PASS with
`ek_match=true dk_match=true` ran while `backend` was 0. With the gate shut it
compared scalar against scalar and proved nothing about the kernel.

### Blockers, unchanged or newly specific

1. `test/01_unit/os/crypto/x25519mlkem768_pinned_workload_spec.spl` now exceeds
   the light daemon cap. `LIGHT_REQUEST_MAX_TIMEOUT_MS = 600000`
   (`src/app/test_daemon/light_protocol.spl:1-2`) clamps `--timeout`, and
   `SIMPLE_TIMEOUT_SECONDS=0` does **not** lift it. A plain `bin/simple test`
   reports `test daemon timed out` instead of a verdict; the passing run only
   completed because it was launched detached and outlived the client. Needs a
   concrete todo — a spec that cannot be run by its normal command is not
   runnable.
2. `qualified_timing.spl:187-194` accumulates `material = material + ...`
   quadratically into an interpreted `sha256_text`: 10 calls at 30 samples plus
   1 at 1025 samples = **124s CPU**. Needs native codegen or a cheaper digest.
3. The backend matrix spec still emits no `Results:` line even after the fixture
   restore, so the spec that pins the backend-id encoding provides no coverage
   of it yet.

### Independent oracle verdict on the AVX2 NTT kernel (closes the gap left at push)

`0aac0a06d23` landed before its independent verification returned. That gap is
now closed, and the result is PASS.

The oracle was built by a lane that never read the kernel, from FIPS 203 first
principles: gamma_i = 17^(2*BitRev7(i)+1) computed at run time, forward
transform evaluated directly as `NTT(f)[2i] = sum_m f[2m]*gamma_i^m`, inverse
from the derived orthogonality relation with 128^-1 obtained by Fermat
exponentiation. No constant hand-entered.

**The scalar reference itself was validated first — the check only this lane
could make.** The implementing lane compared its kernel *against* scalar
`ntt`/`intt`, so had the scalar been wrong, "0 failures" would have certified a
shared error rather than correctness.

  fwd_vs_direct_bad=0        217/217 vectors vs direct O(n^2)
  intt_vs_direct_bad=0       27 vectors (all edges + every 20th)
  roundtrip_bad=0            217/217; out_of_range_coeffs=0 over 55,552
  linearity_bad=0 of 50      convolution_bad=0 of 3 (negacyclic vs base-mul)
  zeta_table_mismatches=0    in-tree table == computed 17^BitRev7(i)
  zeta17_pow128=3328 (=q-1), zeta17_pow256=1, computed_128inv=3303

Kernel verdict, against the landed file:

  ORACLE_KERNEL verdict=PASS backend=1 corpus=217 total=502 mismatches=0
  kernel_fwd_bad=0 kernel_inv_bad=0 scalar_vs_truth_bad=0
  kernel_vs_truth_bad=0 out_of_range=0 first_bad=none

Provenance verified: the `simd.spl` that run loaded is md5
`13fd103b9a6b903096e1f1bcb7e418fc`, byte-identical to
`git show 0aac0a06d23:src/lib/nogc_sync_mut/simd.spl`. No claim by the
implementing lane was refuted.

Conventions confirmed for `src/os/crypto/ml_kem_ntt.spl`: representative range
`[0,q)` non-negative (`modq` :95-101, every `ntt` write via :167-168, empirically
0 out-of-range); `intt` DOES fold the scaling at :211-214 as `* 3303 % q`, where
3303 = 128^-1 (seven butterfly layers, NOT 256^-1), reproduced independently as
`opow(128, q-2)`; no Montgomery, no Barrett, no lazy reduction — plain `%`
(grep for montgomery/barrett/qinv/2285/1441 = 0 hits).

**Coverage gaps, on the record rather than implied covered:**

1. **Only length 256 was exercised.** The kernel was widened mid-run to any
   positive multiple of 256, and `ml_kem_kpke.spl:501-507` passes **768** and
   converts a length mismatch into `Err`, not a fallback. That path is
   independently unverified. This is the most valuable remaining check.
2. `chunk_hits` (80 at 256, 240 at 768) and the AVX2 execution receipt were not
   independently verified; the oracle observed `backend=1` and correct values only.
3. Constant-time / timing behaviour not examined by the oracle.
4. Everything ran on the Rust **seed** interpreter, never the self-hosted binary
   and never native codegen.
5. ~~The consolidated driver never emitted its own verdict line.~~ **Now
   resolved** — it completed:

       ORACLE_MLKEM verdict=PASS total=956 mismatches=0 scalar_fwd_bad=0
       scalar_roundtrip_bad=0 scalar_inv_bad=0 linearity_bad=0 conv_bad=0
       zeta_table_bad=0 range_bad=0 kernel_present=1 kernel_checked=434
       kernel_bad=0 first_bad=none

   Run 1 had aborted at phase 6, vector 125 of 217, with
   `execution limit exceeded: 10000000 operations` and **no verdict line** —
   phases 0-5 had already printed clean counters, so the log read as success.
   That is a third ceiling, distinct from the 60s CPU guard
   (`SIMPLE_TIMEOUT_SECONDS`) and the 600s daemon clamp, and neither of those
   knobs lifts it. Cleared with `rt_fault_set_execution_limit(0)`, proven
   positionally: run 1 died at 125/217, run 2 passed 150, 175, then finished.

### 768 / multi-block path verified — the last high-value gap is closed

The previous entry named the 768-coefficient path as the most valuable remaining
check, because `ml_kem_kpke.spl:476/483` calls `provider.forward/inverse` with a
flattened poly-vector (768 at k=3) and `:505-508` turns a length mismatch into
`Err`, **not** a fallback. Verified independently, against the landed kernel.

**Semantics** (re-confirmed from the non-SIMD branch beside the SIMD one):
`_split_poly_vec` :451-464 takes contiguous 256-blocks (`poly[j] = values[i*256+j]`);
`_vec_ntt_mode` :411-420 transforms **each block independently**; :513 reflattens.
So the required identity is
`batch(x, inv) == concat(ntt(x[0..256]), ntt(x[256..512]), ntt(x[512..768]))` —
**not** a single 768-point transform. That distinction is the real risk: a long
transform would return 768 values and satisfy every length check while being
entirely wrong, so only per-block value comparison can catch it.

    ORACLE_MULTIBLOCK verdict=PASS total=116 mismatches=0 backend=1
      kernel768_checked=80 kernel768_bad=0 kernel768_empty=0
      ground_truth_768_checks=80 scalar768_vs_truth_bad=0 whole_vs_concat_bad=0
      multiples_bad=0 nonmultiple_accepted=0
      chunk_hits_256=80 chunk_hits_512=160 chunk_hits_768=240 chunk_hits_1024=320
      chunk_hits_linear=yes keygen=identical first_bad=none

- **80 of 80 checks at 768 against an independent per-block O(n^2) evaluator** —
  not against the kernel, not against scalar alone. The single-long-transform
  failure mode is excluded: it would have failed every per-block comparison.
- **Block independence 0/10 bad.** Contrast cases (`zeros|impulse|q-1` and its
  rotations, AAB/ABA/BAA/AAA, impulse in first/mid/last only), plus
  `kernel(768) == concat(kernel(256) x3)` on all 10 — the test that would expose
  a shared accumulator or a zeta index not reset per block. A uniform random
  corpus can mask exactly that.
- **512 and 1024 correct** both directions. Non-multiples (1, 255, 257, 300,
  767) all return **length 0**, so the caller's `Err` fires instead of accepting
  garbage.
- **`chunk_hits` scales exactly linearly** with block count: 80/160/240/320.
  Confirms the implementing lane's 80@256 and 240@768, and that the counter
  tracks real work rather than being incremented decoratively.
- **`ml_kem_keygen` vs `ml_kem_keygen_simd` byte-identical** with the gate open
  (backend=1): ek 1184, dk 2400, `ek_first_diff=-1`, `dk_first_diff=-1`.

Provenance: `simd.spl` md5 `13fd103b9a6b903096e1f1bcb7e418fc` (= the landed
blob) and `ml_kem_kpke.spl` md5 `f5a165649ab12fd73574c44ef9841f6f`, stamped
identical before and after every probe.

**Refinement to the earlier `Err` framing:** `ml_kem_kpke.spl:496-497` (and :516)
reject `len == 0 || len % 256 != 0` with `ml-kem-cpu-ntt-input-size-invalid`
**before** the kernel is reached. So the non-multiple case is kernel robustness,
not a live keygen risk — the earlier entry overstated it slightly.

**Still not determined:**
- The op-limit lift is **unproven for this driver**: the A/B twin with
  `rt_fault_set_execution_limit(0)` stripped produced a byte-identical PASS, so
  this run never approached the 10M cap. Both runs did print verdict lines, so
  no truncation occurred. The earlier positional evidence on the 256-driver
  (run 1 died at phase6 125/217; run 2 with the disable passed it) stands but
  was not reproduced here.
- Keygen exercised with **one** deterministic (d,z) pair; non-multiples
  forward-only.
- Everything still ran on the **Rust seed interpreter** — native codegen could
  diverge, and remains the largest untested axis.
- Constant-time behaviour still unexamined.
