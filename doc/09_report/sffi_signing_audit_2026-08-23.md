# SFFI Signing / Verification Audit — 2026-08-23

Question asked: *"is every SFFI binding VERIFIED and SIGNED, or else explicitly
tagged UNSAFE? Nothing should be silently in between."*

**Answer: no, and the premise does not hold. There is no signing mechanism for
SFFI bindings at all — cryptographic or otherwise. 1,501 of 3,959 distinct
extern symbols (37.9%) are in the "neither" class: nothing backs them at
runtime *and* nothing tags them unsafe.**

Measured at `origin/main` `c1efb59cf09` in a detached worktree
(`/mnt/data/worktrees/sffiaudit-1`), using the deployed Rust-seed binary
`bin/release/x86_64-unknown-linux-gnu/simple` (60,650,360 bytes, 2026-08-23
04:47) as the symbol authority via `SIMPLE_BIN`.

---

## 1. What the mechanism actually is

Four things exist. **None of them is signing.** Stated plainly, because the
word "signature" appears throughout this tree meaning *ABI arity/type
signature*, never a cryptographic one.

### 1.1 There is NO cryptographic signing or attestation of SFFI bindings

No signing, no attestation, no manifest hash, no provenance check runs on any
extern declaration, generated wrapper, or dlopen'd provider. Confirmed by
grep across `src/lib/**/sffi/**`, `src/lib/**/ffi/**`, `src/compiler/**/sffi*`
and the docs. The only HMAC signing in the compiler is
`src/compiler/35.semantics/lint/agent_signing.spl`, which signs **lint result
records** for agent-to-agent verification — it has nothing to do with FFI and
is not evidence of an SFFI signing path.

The closest designed thing is **planned, not built**:
`doc/00_llm_process/layer_expert/sffi_boundary/skill.md` ends its pipeline with
"loader admission **(planned P3/P4)**". Loader admission is where a signing or
attestation gate would live. It does not exist today.

### 1.2 `FfiManifest` arity validation — implemented, and DEAD

`src/lib/nogc_sync_mut/ffi/ffi_signature.spl` (mirrored at
`src/lib/{nogc_sync_mut,nogc_async_mut}/sffi/sffi_signature.spl`) defines
`FfiSignature{name, arg_count, return_type}`, `FfiManifest`,
`validate_library(lib, manifest)` and `validate_subset(...)` against a
`VersionedDynLib`.

**Zero production call sites.** `grep -rn 'FfiManifest|validate_library'
--include=*.spl src test` returns only its own definition plus
`test/01_unit/lib/ffi/ffi_signature_spec.spl` (and its `test/unit/` mirror).
Nothing in `src/**` ever builds a manifest or validates a loaded library. This
is the same defect shape as `interface_digest_of` (defined canonically, zero
callers — `.claude/rules/commands.md`): a mechanism that exists as code and
runs never. **No SFFI binding in this tree is arity-verified at load time.**

### 1.3 `@unsafe(reason: ..., capabilities: [ffi])` — the real tagging contract

This is the actual "tagged UNSAFE" surface, and it is a genuine, well-formed
annotation carrying a human reason string, e.g.

    @unsafe(reason: "raw libtorch ABI; foreign implementation is not compiler-validated", capabilities: [ffi])

134 such occurrences for libtorch, 77+75 Cranelift, 72 TRACE32, 57+37 Vulkan,
34 CUDA, and a long tail. It appears in **112 files tree-wide**
(106 under `src/`). HIR models it as `UnsafeCapability.Ffi`.

### 1.4 `raw_sffi_call` / RAW-RT-001 lint — live, but **`allow` by default**

`src/compiler/35.semantics/lint/raw_sffi_call.spl` states the contract exactly:
"A raw extern declaration is an ABI assertion the compiler cannot validate.
Calls must therefore live in the smallest function carrying an explicit
`@unsafe(... capabilities: [ffi])` boundary." It is genuinely wired —
exported at `35.semantics/lint/__init__.spl:178-180`, invoked at
`90.tools/lint/_LintMain/lint_checks.spl:281,560-561`.

**But `config_and_model.spl:230` sets `levels["raw_sffi_call"] = "allow"`.** It
is only raised to `deny` inside `_strict_robust_levels` (`:284`), i.e. under
the Robust/Critical tiers. On the default profile the rule that enforces
unsafe-tagging of raw SFFI calls **emits nothing**. That is precisely the
"silently in between" state the audit asked about, and it is the single
highest-leverage finding in this report.

The companion `raw_rt_access` (RAW-RT-001/002/003, `raw_rt_access.spl`) *is*
`warn` by default — but a warning is not a gate, and it covers `extern fn rt_*`
outside a provider, not the `@unsafe` boundary requirement.

### 1.5 What *does* run: ratchets, not verification

Three fail-closed shell guards constitute the only enforcement in practice:
`check-unbacked-extern-ratchet.shs` (freezes the unbacked population, fails on
NEW ones), `check-no-direct-rt.shs` (baseline 11,816 forbidden direct `rt_*`
call sites), and `check-no-unresolved-runtime-symbols.shs` (currently RED: 83
codegen-emitted names undefined in the C runtime archive). These freeze debt.
They do not verify any binding.

**Consequence, unchanged from `doc/08_tracking/bug/unregistered_extern_silent_nil_2026-08-01.md`:
an extern with no runtime backing silently returns nil instead of failing.**
Every one of the 1,501 symbols below is a potential silent-nil site.

---

## 2. Classification counts

Census produced by the project's own single source of truth,
`sh scripts/check/extern-backing-census.shs` (reads DEFINED symbols out of real
link artifacts via `nm`; not text-grep). Full run, exit 0, 3,959 distinct
extern symbols:

| census class | count | treated as |
|---|---:|---|
| `in_deployed_binary` | 1,452 | backed |
| `interp_extern_registry` | 686 | backed |
| `libc_libm` | 59 | backed |
| `bare_exempt` | 38 | backed (freestanding by design) |
| `GENUINELY_MISSING` | 1,097 | **unbacked** |
| `c_runtime_source_only` | 265 | **unbacked** (source exists, absent from binary) |
| `DEAD_DECLARATION` | 223 | **unbacked** |
| `SHADOWED_BY_SPL_FN` | 82 | **unbacked** |
| `rust_source_feature_gated` | 47 | **unbacked** |
| `external_library_symbol` | 10 | **unbacked** (dlopen-dependent) |
| **TOTAL** | **3,959** | |

**Definition, stated so the numbers reconcile:** "unbacked" here means *all six
non-backed census classes* above, not the two (`GENUINELY_MISSING` +
`DEAD_DECLARATION`) that `check-unbacked-extern-ratchet.shs` freezes. The audit
question is "verified or tagged", not "in the ratchet", so a symbol whose only
backing is C source absent from the binary, or a feature-gated Rust definition,
or an optional dlopen'd library, counts as unbacked here while the ratchet does
not track it. Reconciling the 1,501 headline against the 1,469-row baseline
without this sentence would wrongly suggest the classifier disagrees.

Cross-tabulated against `@unsafe(... [ffi])` tagging (file-level attribution:
a symbol counts as *tagged* if its declaring file carries an `@unsafe` with the
`ffi` capability — this is deliberately **generous**, so the "neither" figure
is a floor, not a ceiling):

| | tagged `@unsafe([ffi])` | untagged |
|---|---:|---:|
| **backed** (nm-resolvable) | 552 | 1,683 |
| **unbacked** | 223 | **1,501** |

- **verified + signed: 0.** Nothing is signed; nothing is arity-verified
  (`FfiManifest` is uncalled). The best available proxy for "verified" is
  *backed* — a real defined symbol in a real link artifact — which is 2,235.
- **explicitly unsafe-tagged: 775** (552 backed + 223 unbacked).
- **neither: 1,501 (37.9%)** — unbacked *and* untagged. 1,445 of these are
  under `src/` (56 are in `test/`); **1,224 have live module-scoped call
  sites**, so they are not dead paper.

Cross-check against the frozen baselines, as required: this census's
`GENUINELY_MISSING + DEAD_DECLARATION` = 1,320 versus
`scripts/check/unbacked_extern_baseline.txt` = 1,469 rows. The gap is
explained by the census here running against a *different deployed binary*
than the one the baseline was frozen on (more symbols now resolve
`in_deployed_binary`), not by a different classifier — the same script produced
both. The numbers are the same order and the same shape, so the classifier is
trusted. **No baseline was regenerated and no guard was weakened for this
audit.**

## 3. The "neither" list

Full list of all 1,501 symbols, with class, module-scoped call-site count and
declaring file: **`doc/09_report/sffi_signing_audit_2026-08-23_neither.tsv`**
(committed alongside this report; it is four digits long and does not belong
inline).

Concentration, for the 1,224 entries under `src/` that have live call sites:

| declaring area | count |
|---|---:|
| `src/compiler_rust/lib/std` | 183 |
| `src/os/kernel/arch` | 175 |
| `src/lib/nogc_sync_mut/io` | 115 |
| `src/lib/nogc_sync_mut/gpu` | 79 |
| `src/app/io/graphics2d_sffi.spl` | 47 |
| `src/lib/gc_async_mut/gpu` | 34 |
| `src/compiler/90.tools/sffi_gen` | 33 |
| `src/os/drivers/virtio` | 32 |
| `src/app/io/http_ffi.spl` | 24 |
| `src/os/kernel/loader` | 23 |
| `src/os/tls13/_Tls13` | 23 |
| `src/os/kernel/boot` | 21 |
| `src/lib/gc_async_mut/net` | 19 |
| `src/app/io/gamepad_sffi.spl` | 19 |
| `src/lib/nogc_sync_mut/ffi` | 18 |

Highest-call-count offenders: `log_raw_println`, `spl_load_i64`,
`rt_push_byte`, `spl_store_u8`, `unsafe_addr_of`, `spl_load_u8`,
`spl_store_i64`, `array_is_valid`, `array_items`, `arm_fs_exec_trace`,
`array_len_value`, `mmio_read8`.

## 4. Ranked risk assessment

1. **`raw_sffi_call` is `allow` by default (config_and_model.spl:230).** The
   one compiler check that enforces the `@unsafe([ffi])` boundary is silent on
   every ordinary build. Everything else in this report is downstream of it.
   Highest leverage, smallest surface: a single line — but promoting it to
   `warn` today would emit on the order of 1,500+ sites, so it needs a
   baseline-and-ratchet like `silent_default`, not a flip. Filed, not flipped.
2. **`src/os/kernel/arch` (175) + `src/os/drivers/virtio` (32) +
   `src/os/kernel/{loader,boot}` (44).** Untagged, unbacked, live MMIO and
   boot-path externs (`mmio_read8`, `spl_load_u8`, `spl_store_i64`). Silent-nil
   here is a wrong *address*, not a wrong value. Many are legitimately
   freestanding, but they are **not** in the 38 `bare_exempt` set, so they are
   claiming host backing they do not have.
3. **`src/os/tls13/_Tls13` (23).** Untagged unbacked externs on a TLS
   implementation path; a silently-nil crypto primitive is a security failure
   that fails *open*.
4. **`FfiManifest` being dead (§1.2).** Every `dlopen`'d provider
   (`sffi/dynamic.spl`, `dynamic_versioned.spl`, `guest_dlopen.spl`,
   `llvm_loader.spl`) is entered with zero arity checking, despite the checker
   being written, tested, and exported.
5. **`external_library_symbol` (10) untagged.** SDL/GL/CU/VK symbols resolved
   only if the library happens to be present at runtime — the archetype of
   silent-nil-on-absent-provider.
6. **`c_runtime_source_only` (98 in the neither set).** C source defines them;
   the deployed binary does not export them. Same class as the still-RED
   `check-no-unresolved-runtime-symbols.shs` (83 codegen-emitted names missing
   from the archive) that produced the stage3 SEGV.
7. **`SHADOWED_BY_SPL_FN` (82).** A pure-Simple `fn` of the same name exists,
   so which one binds depends on module resolution order. Ambiguous, not
   merely unbacked.
8. **1,683 backed-but-untagged.** Lowest risk (the ABI is real) but still
   outside any `@unsafe` boundary, so no reason string documents the contract.

## 5. What was NOT done, and why

- **No declarations deleted.** The prior Stage-2 finding stands: of 262
  `DEAD_DECLARATION` symbols, **zero were actually dead** (70 had a real `.spl`
  call site elsewhere, 41 had non-`.spl` references, 111 were documented public
  API). The dead-code argument was tried and disproven; this audit does not
  retry it. The 223 `DEAD_DECLARATION` rows here are reported, not touched.
- **No mass `@unsafe` tagging.** At 1,501 symbols the "small and clearly
  correct fix" branch is not available. Mechanically stamping `@unsafe` onto
  1,501 declarations would convert a measurable gap into an unreviewed claim
  that each boundary was inspected. Bug records instead (§6).
- **No baseline regenerated, no guard weakened.**

## 6. Filed

`doc/08_tracking/bug/sffi_no_signing_raw_sffi_call_default_allow_2026-08-23.md`
records three concrete items: (a) `raw_sffi_call` default `allow` +
the baseline-and-ratchet promotion path; (b) `FfiManifest` dead wiring;
(c) the 1,501-symbol neither-class with the OS/TLS subsets prioritised.

## 7. Reproduce

```sh
git worktree add --detach <dir> origin/main
export SIMPLE_TIMEOUT_SECONDS=0
SIMPLE_BIN=<path>/bin/release/x86_64-unknown-linux-gnu/simple \
  sh scripts/check/extern-backing-census.shs census.tsv
grep -rlE '@unsafe\([^)]*\bffi\b' --include=*.spl src test > unsafe_files.txt
# cross-tab census.tsv 'first_declaring_file' against unsafe_files.txt
```
