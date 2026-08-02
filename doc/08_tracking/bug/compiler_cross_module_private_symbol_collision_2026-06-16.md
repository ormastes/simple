# Bug: private (`_`-prefixed) functions collide across modules — wrong fn called

- **ID:** compiler_cross_module_private_symbol_collision_2026-06-16
- **Severity:** P1 (silent wrong-result + SIGSEGV; broad latent surface)
- **Status:** MITIGATED — detection diagnostic implemented (option 3). Auto-fix
  (per-file mangle) deferred as a deliberately-scoped effort given measured surface.
- **Area:** compiler — import loader / module flattening / symbol resolution

## Live crash evidence + dormancy status (2026-06-16)
This bug was **actively crashing**, not theoretical. Kernel log (`journalctl -k`,
Jun 15 11:05 → Jun 16 04:26) recorded **18 `simple-main` segfaults**:

| fault addr | count | meaning |
|------------|-------|---------|
| `0x8`  | 14 | NULL+8 field deref (`nil.len()` on a lost return) — JIT-compiled code, no `in simple[...]` module |
| `0x0`  | 2  | NULL deref |
| `0x40` | 2  | small-offset deref in the AOT `simple` binary |

The `0x8` cluster is the exact signature of this bug: a private helper whose
return value was silently dropped → `nil` → NULL-deref under Cranelift JIT.

**Now dormant, not live.** The only confirmed live trigger — `quic_aead_encrypt`
(its module co-imported `aes_gcm._append_bytes(->[u8])` + `hkdf._append_bytes(void)`)
— was fixed the same day by renaming the aes_gcm helper (see
`quic_aead_encrypt_fails_interp_segfaults_jit_2026-06-16`) and the detection
diagnostic below. A **bounded `bin/simple check` sweep (2026-06-16)** over
representative high-fan-in entry points across the crypto / http / compress / tls /
quic namespaces produced **0 live co-import collision warnings**: no current
top-level compilation co-imports an incompatible same-named pair. The 267-name
surface remains **LATENT** — it bites only if a future import graph pulls two
incompatible defs into one compilation.

**Why the structural fix is not landed here.** The full fix (per-file mangle /
file-identity threading in the seed) requires a seed rebuild + full-suite
regression + redeploy and is high-blast-radius (every call in every program), with
`E∩H` non-empty (mangling a genuinely-shared helper like `_hex_digit` orphans its
17 callers). Attempting it speculatively — especially in a shared repo with
parallel agents force-pushing `main` — risks breaking the seed everything depends
on, for a bug whose live trigger is already fixed. It stays a deliberately-scoped
follow-up; the crash path is closed by the rename + detection + (separately) the
codex runaway guard that contains any blast radius.

## Fix landed 2026-06-16 (detection diagnostic)
`warn_duplicate_private_signatures()` in `pipeline/module_loader.rs` runs on every
top-level `load_module_with_imports`: when 2+ co-compiled top-level free functions
share a bare `_`-prefixed name but have differing signatures, it emits a non-breaking
`warning:` to stderr naming the conflicting signatures (process-deduped). Fires only
when an incompatible pair is actually co-imported (low noise), e.g.:
`warning: private helper '_append_bytes' has 2 co-compiled definitions with 2
differing signatures (([i64],[i64])->() vs ([u8],[u8])->[u8]); ... Rename ...`.
Verified: warns on gzip+hkdf `_append_bytes`; quic_aead 3/0 + NIST 12/0 stay green;
broad cross-section = 0 new failures, 0 panics (read-only). Seed rebuilt + redeployed.
The aes_gcm/hkdf case that caused the original SIGSEGV would now warn at compile time.

## Summary
Private helper functions (conventionally `_`-prefixed, file-local by intent) are not
namespaced per file/module. Two modules that each define a function with the same
name but different signatures collapse to one symbol; calls dispatch to whichever
was registered last — nil/garbage in the interpreter, NULL-deref SIGSEGV under the
Cranelift JIT. A callee can silently lose its return value.

## TRUE root cause (verified by instrumented build, 2026-06-16)
The compiler does NOT carry file/module identity to the function registry:
- `load_module_with_imports_internal` (pipeline/module_loader.rs:1203) **flattens
  every imported file's items into ONE `Module`**. The ast `Module`
  (parser/ast/nodes/core.rs:979) is just `{ name: Option<String>, items: Vec<Node> }`
  — there is **no per-item source-file field**. After load, `aes_gcm.spl`'s and
  `hkdf.spl`'s functions are anonymous siblings in one flat `items` list.
- `HirFunction.module_path` (hir/types/functions.rs:26) is set from
  `self.module.name.unwrap_or_default()` (module_lowering/function.rs:737). For the
  merged module that name is `None` → `module_path == ""` for ALL functions.
  **Confirmed empirically:** an instrumented bootstrap build printed
  `PROBE_MODPATH name=_append_bytes module_path=""`.
- `Span` (parser/token.rs:52) carries only `start/end/line/column` — **no file id**.
- Registry + lookup are bare-name: `available_functions`/`function_param_types`
  (mir/lower/lowering_core.rs:1085), codegen `func_ids` (codegen/common_backend.rs:998,
  last-write-wins), JIT/interp lookup (codegen/instr/calls.rs:2972; interpreter
  `HashMap<String, Arc<FunctionDef>>`).

So there is no point downstream of the loader where a call can be attributed to its
defining file. The identity is destroyed at load-time flattening.

## Concrete instance (already worked around)
`aes_gcm.spl:_append_bytes(->[u8])` shadowed by `hkdf.spl:_append_bytes(void)` once
`quic_crypto` imported both → `aes128_gcm_encrypt` returned nil → SIGSEGV. Worked
around by renaming aes_gcm's helper to `_aesgcm_append_bytes` (commit fc08b814).
See `quic_aead_encrypt_fails_interp_segfaults_jit_2026-06-16`.

## Scope of the landmine (MEASURED 2026-06-16 across 18,296 src files)
This is **pervasive, not isolated**: **267 private names** have ≥2 differing-signature
definitions (the harmful set H). Examples: `_u8_at` (35 files, `[u8],i64` vs `[u8],u64`),
`_append_bytes` (31), `_slice_bytes` (17), `_read_u32_le`/`_read_u16_be`/`_text_to_bytes`,
`_sqrt`/`_sin`/`_cos` (f32 vs f64), `_is_digit`, etc. The codebase systematically reuses
file-local private helper names with incompatible signatures; flattening only "works"
because usually one definition is in scope per compilation. The bug bites whenever 2+
incompatible defs are co-imported (as in quic→aes_gcm+hkdf).

**E∩H is non-empty.** `_hex_digit` is BOTH harmful (6 differing sigs) AND genuinely
shared cross-file (called in 17 files that do NOT define it). So per-file mangling is
NOT blindly safe: mangling `_hex_digit`'s def would orphan its 17 callers. A safe
auto-mangle must (a) use a real parse (not regex) for accurate signatures, (b) exclude
every name in E, and (c) rewrite the full 267-name surface with an exhaustive AST
walker + orphan-scan backstop. That is a large, high-blast-radius change — far beyond
the "handful of names" originally assumed.

**Re-scoped recommendation:** the right-sized, safe compiler fix is **per-compilation
collision DETECTION that hard-errors** — at the post-flatten point, if 2+ functions
share a name but differ in signature/return-arity, emit a compile error naming both
(the aes_gcm/hkdf case would have errored loudly instead of SIGSEGV). This closes the
safety hole (no more silent mis-dispatch) without a 267-name rewrite, and prompts a
targeted rename (as already done for aes_gcm). Auto-mangle remains possible but should
be a separate, deliberately-scoped effort given the measured surface.

## Fix options (each requires a seed rebuild + full-suite regression + redeploy)
1. **Per-file mangle at the loader boundary** (module_loader.rs, where `path` IS in
   scope per recursion): before merging a file's items, rename its private (`_`)
   top-level fn defs + rewrite that file's own call sites to `name$<file-hash>`.
   Deterministic. Needs a complete AST call-site renamer (no general-purpose AST
   mutator exists today — only `monomorphize/rewriter.rs`-style special-purpose
   passes), and a `log()` for any residual call to a private name with no same-file
   def. Medium surgery, localized to the loader.
2. **Thread file identity AST→HIR**: add a source-file field to items/functions,
   populate `module_path` from it, then a single post-merge mangling pass over
   `hir.functions` keyed by `(module_path, name)` + body call-rewrite. Larger surgery
   (AST + loader + HIR) but fixes the underlying "identity never propagated" deficit.
3. **Detection lint (stopgap, no auto-fix)**: flag two in-scope private fns with the
   same name and differing signature/return arity. Fails loud instead of silent
   mis-dispatch; cheap; does not unblock legitimate same-name private helpers.

Blast radius of 1/2 = every function call in every program → a broad cross-section
of the suite must be run against `target/bootstrap/simple` BEFORE redeploying to
`bin/release/.../simple_seed`. The self-hosted `src/compiler` likely has the same
flattening and is a separate follow-up.

## Notes
Related: `rt_extern_registration_and_jit_cross_module_gap` (imported class methods →
NULL-GOT). This is the private-function analogue and corrupts even the interpreter,
so it is not caught by the existing JIT first-unresolved-import guard.

## Same-signature collision resolution — batch 1, crypto/TLS stack (2026-08-02)

Base sha `aa6119dd768098aa0bb5b7b335f82f101c2e98ca`. Binary: Rust driver built from
that sha (enum-probe = 0), because the same-signature arm of the diagnostic lives in
`src/compiler_rust/compiler/src/pipeline/module_loader.rs` and the deployed
`bin/release/x86_64-unknown-linux-gnu/simple` does not contain it (`strings | grep -c
"SAME signature"` = 0). PROVED.

### Diagnostic control (PROVED)
Two-module fixture (`ca.spl`/`cb.spl` each `fn who() -> text`, third file importing
both) fires the warning and prints `A` — first-import-wins, matching the corrected
policy table in the loader doc comment. The control is therefore verified PRESENT
before any "no longer warned" claim below.

### Runner stack is clean (PROVED)
A 3-example spec importing only `std.spec.{describe, it, expect}` produces ZERO
same-signature warnings. The collisions are NOT in the runner stack; they are in the
subject modules a spec pulls in. This contradicts the "every spec pulls in the runner
stack" framing of the 313 figure — that count came from a spec with a much wider
subject surface, not from the runner.

### Static census, before/after exclusions (PROVED)
Over `src/**/*.spl`, excluding `build/`, `.claude/`, `vendor/`:

| stage | count |
|---|---|
| files enumerated | 13,790 |
| after byte-identical duplicate-content exclusion | 13,160 (−630) |
| bodyless `extern fn` headers excluded | 9,314 |
| top-level `fn` declarations remaining | 82,178 |
| names declared in >= 2 distinct files | 7,883 |
| declaration sites participating in a collision | 21,765 |

This is a gross upper bound: it does not model co-compilation. `main` alone accounts
for 565 sites and is almost never co-compiled. INFERRED that the live figure is one
to two orders of magnitude smaller; see the measured numbers below.

### Live enumeration, TLS 1.3 / crypto cluster (PROVED)
`SIMPLE_DIAG_SAME_SIGNATURE_COLLISION=1 simple run
test/01_unit/os/tls13/server_accept_spec.spl` reported 10 distinct same-signature
collisions: `_append_bytes`, `_clamp_scalar`, `_copy_prefix`, `_curve_debug`,
`_rotl32`, `_u32_mask`, `_u8_at`, `_zeros_48`, `msg_schedule1`, `msg_schedule2`.

Two of these are NOT benign duplicates:

- **`msg_schedule1` / `msg_schedule2`** (PUBLIC, `(i64)->i64`): `sha256.spl` computes
  the SHA-256 message schedule inline with a 32-bit mask; `sha256_core.spl` delegates
  to `sha256_little_sigma0`. Different bodies, identical signature. The MIR-opt crypto
  pattern recogniser
  (`src/compiler/60.mir_opt/mir_opt/pattern/rules_crypto.spl:44-45`) keys on the
  fully-qualified `std.common.crypto.sha256.msg_schedule1`, i.e. it expects the
  `sha256.spl` body to be the one that runs — which first-import-wins does not
  guarantee.
- **`_clamp_scalar`** (`([u8])->[u8]`): `curve25519.spl` and
  `curve25519_smalllimb.spl` implement RFC 7748 scalar clamping by different means.
  Which X25519 clamp runs was decided by import order.

`_u8_at` is the worst of the family: 34 definitions, **6 semantically distinct
bodies**, and **91 files that call it without defining it** and therefore depend
entirely on the hijack. The only OOB-tolerant variant (`src/os/tls13/server.spl`,
returns `0u8` past the end) has **zero in-file call sites**, so if it won the race it
silently substituted zero for an out-of-range byte read anywhere in the crypto stack.

### Dispositions applied
- **Renamed to module-unique names** (disposition b — distinct implementations that
  must not share a name), 24 definitions of `_append_bytes` plus the one non-defining
  caller (`src/os/tls13/_Tls13/handshake.spl`, re-pointed at `_rec13_append_bytes`).
  `_append_bytes` now has **0** remaining definitions and **0** remaining calls under
  the bare name.
- **Renamed** `_clamp_scalar`, `_curve_debug` (curve25519_smalllimb), `_rotl32`
  (random/scrypt/serpent/zuc/lib chacha20), `_u32_mask` (random/sha256/lib chacha20),
  `_zeros_48`, `_copy_prefix` (tls13 key_schedule/transcript), `msg_schedule1/2`
  (sha256_core), `_u8_at` (tls13 server).
- **Left alone, deliberately**: the 33 remaining `_u8_at` definitions. They cannot be
  renamed piecemeal — 91 non-defining callers resolve through the bare name today, so
  renaming them would convert a silent wrong answer into a build break across the
  whole crypto stack. The correct fix is one canonical shared byte accessor that all
  of them import. Filed as follow-up, NOT a triage question to be reopened.

### Reroute-behaviour verification (PROVED)
Every renamed helper except `_append_bytes` had **all** of its callers inside its own
defining file (checked by definer-set vs caller-set difference), so those renames
cannot reroute anything. For the one genuine re-point,
`_Tls13/handshake.spl` previously resolved `_append_bytes` through first-import-wins
among `record13`/`handshake13`/`_Tls13/context_io` — all three bodies were read and
concatenate `a` then `b` identically, so `_rec13_append_bytes` preserves behaviour
(body equivalence PROVED by reading; the identity of the previous winner is
INFERRED).

Two worktrees at the same base sha, 16-spec crypto/TLS verification set:

| | BASE | after renames |
|---|---|---|
| failing example NAME set | 3 | 3, `diff` clean |
| per-spec exit codes | — | identical |
| live same-signature collisions | 50 | **25** |

`server_accept_spec` alone went 10 -> 1. The three failures are pre-existing at the
base sha and are unrelated (CertificateVerify signing path).

### Not done in this lane
The warning was NOT promoted to fatal (out of scope, and the measured runtime figure
bounds the interpreter path only).

`simple test` binds the child's stderr into a value via `process_run_bounded`, so a
spec's own collision warnings never surface under `test`. All enumeration above was
done with `simple run` for that reason. Mechanism INFERRED, invisibility PROVED.
