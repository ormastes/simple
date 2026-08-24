# SFFI bindings are neither signed nor arity-verified, and the lint that would require an `@unsafe` tag is `allow` by default

- **Status:** PARTIALLY FIXED — exact unsafe-declaration ratchet landed; default call lint promotion remains open
- **Filed:** 2026-08-23
- **Measured at:** `origin/main` `c1efb59cf09`
- **Audit:** `doc/09_report/sffi_signing_audit_2026-08-23.md`
- **Full offender list:** `doc/09_report/sffi_signing_audit_2026-08-23_neither.tsv`
- **Related:** `doc/08_tracking/bug/unregistered_extern_silent_nil_2026-08-01.md`
  (the silent-nil defect class), `scripts/check/check-no-unresolved-runtime-symbols.shs` (RED, 83 names)

## Summary

An audit of the whole SFFI surface found **no signing or attestation mechanism
of any kind** for SFFI bindings, and **no arity verification actually running**.
Of 3,959 distinct extern symbols, **1,501 (37.9%) are unbacked at runtime AND
carry no `@unsafe(... capabilities: [ffi])` tag** — the "silently in between"
class. 1,224 of those have live module-scoped call sites. Because an unbacked
extern **silently returns nil instead of failing**, each is a potential silent
wrong-value site.

## Three concrete defects

### D1 — `raw_sffi_call` lint is `allow` on the default profile

`src/compiler/90.tools/lint/_LintMain/config_and_model.spl:230`

    levels["raw_sffi_call"] = "allow"

It is raised to `deny` only in `_strict_robust_levels` (`:284`), i.e. the
Robust/Critical tiers. The rule itself is correct and fully wired
(`35.semantics/lint/raw_sffi_call.spl`, exported at `lint/__init__.spl:178-180`,
invoked at `_LintMain/lint_checks.spl:281,560-561`) and states the contract:
raw extern calls must live in the smallest function carrying an explicit
`@unsafe(... capabilities: [ffi])` boundary. On the default profile it emits
nothing, so that contract is unenforced everywhere it matters.

**Do NOT simply flip the line.** Promoting to `warn` today would fire on
~1,500+ sites. The correct path is the one already used for `silent_default`
(`config_and_model.spl:231-239`): add a fail-closed baseline check
(`scripts/check/check-raw-sffi-call-baseline.shs`, modelled on
`check-unbacked-extern-ratchet.shs`), freeze the current population, ratchet it
down, and promote to `warn` then `deny` when the baseline reaches 0. A
reproduce test must fail pre-fix.

### 2026-08-24 ratchet checkpoint

`scripts/check/check-raw-sffi-unsafe-ratchet.shs` now freezes the current
untagged declaration identities as `(file, symbol, canonical ABI signature
SHA-256)`. It rejects both new debt and stale rows, recognizes multiline
`@unsafe(... capabilities: [ffi])`, and fails closed when no Simple source is
discovered. The source-only scan is bootstrap-owned because its measured
9.37-second baseline would consume almost the entire interactive push budget.
It performs no provider loading and no runtime-call work.

The frozen baseline contains 12,799 unique untagged identities from 13,852
declaration rows. These are explicitly migration debt, not safe, verified, or
signed declarations. `raw_sffi_call` remains `allow` in the default lint
profile until the debt can be reduced without flooding normal builds.

### D2 — `FfiManifest` arity validation has zero callers

`src/lib/nogc_sync_mut/ffi/ffi_signature.spl` (and the
`{nogc_sync_mut,nogc_async_mut}/sffi/sffi_signature.spl` mirrors) implement
`FfiManifest`, `validate_library(lib, manifest)` and `validate_subset(...)`
against a `VersionedDynLib`. `grep -rn 'FfiManifest|validate_library'
--include=*.spl src test` returns the definition plus
`test/01_unit/lib/ffi/ffi_signature_spec.spl` and its `test/unit/` mirror —
**nothing under `src/**` ever constructs a manifest**. Every `dlopen` path
(`sffi/dynamic.spl`, `dynamic_versioned.spl`, `guest_dlopen.spl`,
`llvm_loader.spl`) admits a provider with no arity check.

Same shape as `interface_digest_of` (canonical, zero call sites — see
`.claude/rules/commands.md`). Fix: wire manifest validation into the versioned
dynamic-load path, failing closed on mismatch. **Do not delete the module** —
it is the correct mechanism, merely unwired.

### D3 — 1,501 symbols neither backed nor tagged

Full list in the audit's `.tsv`. Priority subsets, by blast radius rather than
by count:

1. `src/os/kernel/arch` (175), `src/os/kernel/{loader,boot}` (44),
   `src/os/drivers/virtio` (32) — live MMIO/boot externs (`mmio_read8`,
   `spl_load_u8`, `spl_store_i64`). These are freestanding in spirit but are
   **not** in the 38 `bare_exempt` set, so they claim host backing they lack.
   Either mark them `@extern("bare", ...)` where that is truthful, or tag the
   boundary.
2. `src/os/tls13/_Tls13` (23) — a silently-nil crypto primitive fails **open**.
3. `src/lib/nogc_sync_mut/io` (115), `.../gpu` (79), `src/app/io/*_sffi.spl`
   (90) — the largest userland concentrations.
4. `external_library_symbol` (10) — dlopen-dependent SDL/GL/CU/VK.
5. `SHADOWED_BY_SPL_FN` (82) — a same-named pure-Simple `fn` exists, so binding
   is resolution-order dependent; ambiguous, not merely unbacked.

**Explicitly rejected approaches** (tried and disproven previously; do not
retry): deleting `DEAD_DECLARATION` symbols on a dead-code argument — of 262
audited, **zero** were dead. And mass-stamping `@unsafe` on 1,501 declarations,
which would convert a measured gap into an unreviewed safety claim.

## Documentation gap (fixed in the filing commit)

`doc/07_guide/platform/ffi/sffi.md`, `.claude/memory/ref_sffi.md` and
`doc/00_llm_process/layer_expert/sffi_boundary/skill.md` described the SFFI
boundary without ever stating that there is no signing and no running
verification, which is what let the premise "every binding is verified and
signed" survive. All three now carry the contract explicitly.
