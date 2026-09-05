# `rt_str_hash` has THREE behaviors — the bootstrap capsule runs a TRUNCATED FNV-1a offset basis

- **Filed:** 2026-08-31
- **Severity:** MEDIUM — one exported symbol, three different answers, decided by link lane; no persisted data corrupted (measured, see "Persistence analysis")
- **Status:** RESOLVED 2026-08-31 — `r1` (legacy_core) and `r1b` (rt_hash_text) applied and behaviorally verified on Windows/MinGW (see "Resolution evidence"); the Rust-seed djb2 divergence stays OPEN as its own follow-up
- **Found by:** `doc/08_tracking/test/rt_test_coverage_audit_2026-08-31.md` §7 R1; independently re-verified in this record with corrected counts

## Symptom

`rt_str_hash` is defined in two C translation units with **different** FNV-1a
offset bases, and the Rust seed's definition is not FNV at all:

| lane / file | constant | note |
|---|---|---|
| `src/runtime/runtime.c:541` (`spl_str_hash`, wrapped by `rt_str_hash` at :552) | `14695981039346656037ULL` | correct FNV-1a-64 basis (`0xcbf29ce484222325`) |
| `src/runtime/runtime_legacy_core.c:295` (`spl_str_hash`, wrapped at :304) | `1469598103934665603ULL` | same digit string, **trailing `7` dropped** (19 digits, not 20) |
| `src/compiler_rust/runtime/src/value/collections.rs:4532` (`rt_str_hash` → `rt_hash_text` :4513) | `5381` / `*33` | **djb2, not FNV-1a at all** — a third behavior the audit missed |
| `src/compiler_rust/compiler/src/pipeline/native_project/stubs.rs:723` (compat stub) | `14695981039346656037ULL` | correct basis |

(Audit cited `runtime.c:541` / `runtime_legacy_core.c:243`; in the Windows MAIN
checkout where the fix landed: `runtime.c:548/557`, `runtime_legacy_core.c:244/253`,
`runtime_native.c` rt_hash_text basis at :8107, rt_core_dict_hash at :8302 —
content identical, line numbers drift per checkout.)

The core-C bootstrap capsule
(`scripts/check/build-core-c-bootstrap-runtime-capsule.shs`, `SOURCE_FILES`
list at ~line 94-117) compiles `runtime_legacy_core.c` and **not**
`runtime.c`, so the bootstrap lane runs the truncated constant. The audit
measured this, not inferred it: `nm` on the linked capsule attributes the
definition to `src_runtime_runtime_legacy_core.o`, and `rt_str_hash("")`
returned exactly `1469598103934665603`. Both TUs are recorded as co-defining
the symbol in `scripts/check/runtime_bundle_duplicate_symbols_baseline.txt`,
so in the full bundle **link order** picks the winner.

`rt_str_hash` is reachable from product code: the seed lowers `.hash()` on a
STRING receiver directly to it
(`src/compiler_rust/compiler/src/mir/lower/lowering_expr_method.rs:185`).

## Corrected census (the audit's "8 more files" is wrong — it is 16)

The truncated 19-digit constant appears, outside `runtime_legacy_core.c`, in
**16 owned source files (22 occurrences)** under `src/`, plus 7 files under
`test/` (benchmark checksums). The audit listed 9 of these. Full list
(grep `1469598103934665603`, excluding the correct 20-digit constant and
generated `target/` artifacts):

```
src/app/hal_provider/hal_provider_worker_v1.c:270          IPC frame digest (C side)   <- audit missed
src/app/hal_provider/pure_worker_v1.spl:413                IPC frame digest (spl side) <- audit missed
src/app/ui.chromium/snapshot.spl:163                       pixel-stream rolling hash
src/compiler/35.semantics/lint/lint_cache.spl:13           lint cache key (in-memory Dict)
src/compiler/40.mono/monomorphize/mono_key.spl:61,78       monomorphization key hash
src/compiler_rust/runtime/src/vulkan_graphics_runtime_swapchain.rs:885,961,1019,1115  frame checksums <- audit missed
src/lib/common/ui/render_opt/composition_damage.spl:75     damage-region hash          <- audit missed
src/lib/nogc_async_mut/gpu/store/cas_store.spl:189         CAS digest (in-memory simulation)
src/lib/nogc_sync_mut/engine/audio/ui_click_pcm_raw.spl:46 PCM checksum                <- audit missed
src/lib/nogc_sync_mut/game2d/ports/doomgeneric.spl:61      frame hash
src/os/kernel/loader/installed_artifact_catalog_v1.spl:414 in-kernel key table hash    <- audit missed
src/os/kernel/memory/memory_swap.spl:47                    swap checksum
src/os/services/audio/audio_service.spl:204                audio hash
src/runtime/runtime_directx_core.c:61                      frame checksum
src/runtime/runtime_native.c:8354 (rt_hash_text), 8549 (rt_core_dict_hash)             <- audit missed
src/runtime/runtime_rocm.c:265                             frame checksum
```

Every one of these is an **independent local hasher** — none calls
`rt_str_hash`. They are truncated-basis FNV, which is still a serviceable
non-crypto hash (the audit's severity note stands): the defect is the
`rt_str_hash` divergence, not their distribution.

**Why the truncated constant exists at all:** `14695981039346656037` does not
fit `i64`, and until 2026-08-04 the parser rejected decimal `u64`-suffixed
literals (`doc/08_tracking/bug/parser_decimal_u64_rejected_as_i64_2026_08_04.md`
— the rejected literal was this exact constant). Dropping the last digit made
it fit the signed range. Sites that want the true basis in Simple use the
wrapped form `-3750763034362895579` (e.g. `src/lib/nogc_sync_mut/src/hash.spl:44`,
`src/compiler/70.backend/linker/linker_wrapper_helpers.spl:250`,
`src/app/startup/contract/startup_plan_v1.spl:159`) or compute it from parts
(`src/compiler/70.backend/linker/lib_smf.spl:412`).

## The frozen oracle (CORRECTED at filing time)

An earlier draft of this record said
`test/01_unit/lib/nogc_sync_mut/hash_text_crosslang_spec.spl` freezes the
`rt_hash_text` C oracle at the correct basis. **Stale as filed:** wave-6
(`26de1a115c3`) regenerated that file into generic language-semantics filler —
it contains no hash assertion at all today (verified by grep; it passes 6/6
vacuously with respect to hashing). The alignment anchors that DO pin the
correct basis in-tree are the pure-Simple bridge
`src/lib/nogc_sync_mut/src/hash.spl` (`FNV_OFFSET: i64 = -3750763034362895579`,
and its `pub fn rt_hash_text` ABI bridge) and the executable C selfcheck
`src/runtime/test/rt_core_abi_untested_selfcheck.c` (H0/H1). The C
`rt_hash_text` in `runtime_native.c` used the truncated basis and therefore
contradicted both; companion patch `r1b_rt_hash_text_oracle_alignment.patch`
aligns it. (No FNV KAT was added to a .spl spec on purpose: the interpreter
lane may bind `rt_hash_text` to the Rust seed djb2 implementation, which
would fail such an assert for a reason unrelated to this defect.)

**Dual-run shadow gate (C-MIG-0020) impact of r1b:** the shadow lane
(`test/01_unit/lib/common/spec/dual_run_shadow_spec.spl`, wired pair
"0020 [rt_hash_text only — the sibling rt_str_hash is not registered in the
interpreter's extern dispatch table, deferred]") compares BOTH implementations
live at runtime — there is no recorded baseline of hash values to go stale.
The pure-Simple side (`std.hash`) already uses the correct basis, so r1b moves
the C oracle TOWARD the side it is dual-checked against; it cannot flip that
gate red. Which implementation the interpreter extern currently binds
`rt_hash_text` to (C truncated FNV, Rust djb2, or a Simple bridge) is
untestable at filing time — a test run would write `doc/08_tracking/test/*`
inside the repo and trip the in-flight bootstrap's input gate.

## Persistence analysis (why the constant change is safe)

Checked per site whether the hash is (a) in-memory, (b) persisted, (c) a
content address / cache key:

- **`rt_str_hash` itself: (a) in-memory only.** Dict bucketing uses the
  *static* `rt_core_dict_hash` (`runtime_native.c:8546`, no API accepts a
  precomputed hash), rebuilt per process. No stdlib path persists a
  `rt_str_hash`/`.hash()` result. Decisive evidence: the Rust seed lane has
  been returning **djb2** values for the same calls all along — any persisted
  cross-lane identity built on `rt_str_hash` would already be visibly broken,
  and none is.
- **Persisted formats use their own independent hashers with the CORRECT
  basis:** SMF (`lib_smf.spl:412`, computed from parts), startup plan receipts
  (`startup_plan_v1.spl:159`, `load_plan_receipt.spl:69`), linker wrapper
  (`linker_wrapper_helpers.spl:250`), `std.hash` (`hash.spl:44`). Unaffected.
- **Caches are compiler-fingerprint-keyed** (`object_cache_key` folds the
  compiler binary's own hash; `native_build_cache_scope_key` folds full
  producer identity — see `.claude/rules/commands.md`), so a runtime/compiler
  rebuild that changes hashing invalidates cache directories wholesale anyway.
- **Of the 16 independent sites:** `lint_cache.spl` is an in-memory
  `Dict<text, LintCacheEntry>` (class at :31, no file I/O in the module) —
  (a). `mono_key.spl` states "no pipeline wiring here"; the key identity is
  the canonical TEXT, the hash is derived — (a). `cas_store.spl` is,
  verbatim, a "Pure in-memory CAS simulation for interface-first MMU
  development" — (a) today despite the content-address shape. All checksum
  sites (vulkan/directx/rocm/doom/audio/pcm/swap/damage) are (a).
  **Two protocol-coupled groups exist:** the hal_provider pair
  (`hal_provider_worker_v1.c:270` + `pure_worker_v1.spl:413`) embeds the
  digest in `HALRES1|` IPC frames — the C and Simple sides must change
  **atomically or not at all**; and `snapshot.spl:163` is an input to the
  cross-stage "byte-identical replay" determinism requirement (its own
  comment). Neither calls `rt_str_hash`; neither needs to change.

## Migration recommendation

1. **Safe as a scoped constant change:** apply
   `r1_rt_str_hash_offset_basis.patch` (legacy_core only). No cache-version
   bump required — the value is in-memory-only per the chain above. In-process
   hash tables are rebuilt every run.
2. **Apply the companion** `r1b_rt_hash_text_oracle_alignment.patch` so the C
   `rt_hash_text` oracle matches its frozen spec. `rt_core_dict_hash`
   (static, bucket-internal, value never escapes) is deliberately left alone.
3. **NOT safe as a blind global find/replace.** The hal_provider pair is an
   IPC protocol (atomic-or-nothing); `snapshot.spl` is a cross-stage
   determinism input; and the `i64`-typed `.spl` sites *cannot hold* the
   20-digit decimal — any future edit there must use `-3750763034362895579`
   or `0xcbf29ce484222325`, never the decimal literal.
4. **Separate follow-up (not this record's fix):** the Rust seed's
   `rt_str_hash` = djb2 is a larger lane divergence than the audited one and
   deserves its own decision (align seed to FNV, or document djb2 as
   seed-lane-only).

## Unix impact

The patch changes one integer literal in portable C (`ULL` suffix, C99).
No platform-conditional code touched. Linux/macOS behavior changes exactly as
intended: `rt_str_hash` from the legacy TU returns true FNV-1a-64, matching
`runtime.c` and the native stub. Nothing else.

## Resolution evidence (measured 2026-08-31, Windows/MinGW gcc 15.2.0)

Each C TU was compiled unmodified from the tree, linked into a harness with
only unrelated symbols stubbed, and EXECUTED — before and after the patch:

| probe | legacy_core lane BEFORE | legacy_core lane AFTER | runtime.c reference lane |
|---|---|---|---|
| `rt_str_hash("")` | `1469598103934665603` | `-3750763034362895579` | `-3750763034362895579` |
| `rt_str_hash("abc")` | `-2204510569963675907` | `-1792535898324117685` | `-1792535898324117685` |
| `rt_str_hash("simple")` | `9140951567409697905` | `-5909502519632118881` | `-5909502519632118881` |

`rt_hash_text` (runtime_native.c, r1b) before/after on the same harness:
`rt_hash_text("") = 1469598103934665603 -> -3750763034362895579`,
`rt_hash_text("abc") -> -1792535898324117685` (= FNV-1a-64 KAT
`0xe71fa2190541574b` signed). AFTER matches the `std.hash` pure-Simple bridge
exactly.

`src/runtime/test/rt_core_abi_untested_selfcheck.c`, unmodified:
BEFORE `FAIL H0, FAIL H1, FAIL I5 — 23 check(s), 3 failure(s)`;
AFTER `PASS: 23 check(s), 0 failure(s)`.

Dependency scan for consumers of the OLD truncated hash: grep over `test/`,
`src/`, `doc/08_tracking` for the truncated basis and for the old outputs
(`-2204510569963675907`, `9140951567409697905`) found NO spec or fixture
pinning an `rt_str_hash`/`rt_hash_text` output value. The truncated-basis
hits in `test/` (u64_fnv_literal_stage4_spec, lint_cache_spec,
probe_ui_click_pcm_raw, GPU benches) all mirror INDEPENDENT local hashers
that this fix deliberately does not touch. No test needed updating.
