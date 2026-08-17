# Bug: private (`_`-prefixed) functions collide across modules — wrong fn called

- **ID:** compiler_cross_module_private_symbol_collision_2026-06-16
- **Severity:** P1 (silent wrong-result + SIGSEGV; broad latent surface)
- Status: OPEN (P1)
- Status re-verified 2026-08-17 by source inspection (triage shard 00).
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

## Same-signature collision resolution — batch 2, AES-GCM / GCM-SIV (2026-08-02)

Continued from batch 1 on the same crypto/TLS cluster.

### TOP FINDING — `ed25519_verify` picks its implementation by import order (PROVED)

`ed25519_verify(pubkey: [u8], message: [u8], signature: [u8]) -> bool` has **three
co-compiled definitions with identical signatures**:

| module | body |
|---|---|
| `src/lib/common/crypto/ed25519.spl` | pure-Simple RFC 8032 §5.1.7 verification |
| `src/os/crypto/ed25519.spl` | pure-Simple RFC 8032 §5.1.7 verification, extra rejects |
| `src/lib/nogc_sync_mut/io/signature_sffi.spl` | `rt_ed25519_verify(...) == 1` — native extern |

**26 files call it without defining it**, including `src/os/crypto/jwt.spl`,
`paseto.spl`, `cose.spl`, `src/os/services/update/tuf_signing.spl`,
`src/os/tls13/_CertVerify/signature_verify.spl`, and the sshd/ssh_client key-exchange
paths. Every one of them resolves through the bare-name registry, so **import order
decides whether an Ed25519 signature is verified in pure Simple or handed to the
native runtime**, with no diagnostic other than the opt-in warning.

This compounds with a known JIT defect: an unregistered `@extern fn` returns nil
silently under the JIT only, and `signature_sffi`'s body is `result == 1` on exactly
such a call. A wrong answer here is an authentication-bypass class, not a
correctness nit.

NOT fixed in this lane: choosing a winner among three verification backends is a
security-design decision, and the 26 non-defining callers mean a piecemeal rename
converts the hazard into a build break. Requires a single canonical
`ed25519_verify` that all callers import explicitly.

### Resolved in batch 2 (disposition b — module-unique renames)
`ghash`, `gf128_mul`, `_ghash_block`, `_inc32`, `_make_j0`, `_pad_to_16`,
`_aes_sbox_table`, `_aes_rcon_table`, `_aes128_encrypt_block`,
`_aes256_encrypt_block` across `src/lib/common/crypto/aes_gcm.spl`,
`src/lib/nogc_async_mut_noalloc/tls/aes128_gcm.spl`, `src/os/crypto/aes_gcm.spl`,
`aes128_gcm.spl`, `aes256_gcm.spl`, `aes128_tables.spl`,
`aes_gcm_siv{,_aes_core,_polyval}.spl`, `src/os/services/nvfs/core/crypto/aes128_gcm.spl`.
Each of these had **zero non-defining callers** (checked definer-set vs caller-set),
so no call site was re-pointed and no reroute is possible. All ten names now have
0 or 1 definition repo-wide.

`_bytes_equal` reduced to a single `src/**` definition (`src/os/crypto/ed25519.spl`).

### Deliberately NOT renamed, with reasons (disposition c — recorded so it stops being re-triaged)
Each of these has non-defining callers that resolve through the bare name today.
Renaming them piecemeal trades a silent wrong answer for a build break across the
crypto stack, which is not an improvement without the canonical-helper work:

| name | definers | non-defining callers |
|---|---|---|
| `_u8_at` | 33 | 91 |
| `ed25519_verify` | 3 | 26 |
| `_byte_buf` | 9 | 3 |
| `_copy_range` | 3 | 2 |
| `_aes_sbox` | 7 | 1 (`src/os/crypto/aes128_gcm.spl`) |
| `_aes_rcon` | 6 | 1 (`src/os/crypto/aes128_gcm.spl`) |
| `sha512_hmac` | 2 | 2 (`ecdsa_p521.spl`, `slh_dsa.spl`) |

Also left: spec-local `_bytes_equal` copies under `test/**`. Now that `src/**` has
exactly one definition, a spec that declares its own still forms a 2-way
same-signature collision with it — the classic shim-vacuity shape. Resolving that is
a `test/**` sweep, not part of this crypto lane.

### Verification (PROVED)
Same 16-spec crypto/TLS set, two worktrees at the same base sha:

| | BASE | batch 1 | batch 1+2 |
|---|---|---|---|
| failing example NAME set | 3 | 3 | 3, `diff` clean |
| per-spec exit codes | — | identical | identical |
| live same-signature collisions | 50 | 25 | **13** |

## Broad live enumeration — 63-spec sample (2026-08-02, PROVED)

`SIMPLE_DIAG_SAME_SIGNATURE_COLLISION=1 simple run` over a 1-in-300 sample of the
18,708 `*_spec.spl` files (63 specs), post batch 1+2:

| measure | value |
|---|---|
| specs that hit at least one same-signature collision | **12 / 63 (19%)** |
| distinct colliding names observed | **178** |
| total warning lines | 413 |
| worst single spec (`test/03_system/gui/wm_compare/famous_site_engine2d_backend_spec.spl`) | **145 same-signature vs 12 differing** |

The 145:12 ratio on the worst spec reproduces the reported ~8x same-vs-differing
imbalance independently, on a different spec, after this lane's fixes. The
previously reported 313 is therefore not an outlier.

**The collisions are not in the runner stack.** A 3-example spec importing only
`std.spec.{describe, it, expect}` warns ZERO times (PROVED). 51 of 63 sampled specs
warn zero times. The load is concentrated in wide-surface specs (GUI/engine2d,
browser engine, compiler bootstrap).

### Next-largest family: duplicated stdlib filesystem/env API *within one tier*
The most frequently colliding names in the sample are `file_read`, `file_write`,
`file_exists`, `file_size`, `file_delete`, `file_copy`, `dir_list`, `dir_walk`,
`dir_create`, `env_get`, `env_set`, `host_os`, `host_arch`, `has_avx2`, `has_neon`.

These are **not** intentional tier mirrors — checked, and the collisions are inside a
single tier:

- `file_read` — `src/lib/nogc_sync_mut/database/atomic.spl` vs
  `src/lib/nogc_sync_mut/database/core.spl`
- `env_get` — `src/lib/nogc_sync_mut/io/env_ops.spl` vs
  `src/lib/nogc_sync_mut/io_runtime.spl`

`env_get` in particular already has its own bug record
(`interp_env_get_name_collision_nil_root_2026-07-26`); this diagnostic now shows it
is one member of a ~15-name family with the same shape. That family is the natural
next batch and is a `src/lib/nogc_sync_mut/**` lane, not a crypto lane.

---

## Re-measured 2026-08-17 (CRITICAL lane, slice C1b) — CONFIRMED LIVE, and BROADER than filed

Verdict rests on **EXECUTION**, not source reading. Reproduced with `bin/simple run`
(Rust seed, the currently deployed binary) on purpose-built two-module fixtures.

### The title understates the defect on three axes

**1. Not specific to `_`-prefixed private functions.** A public `fn who() -> text`
defined in two co-compiled modules collides identically:

```
$ bin/simple run pmain.spl     # use pa.{call_a}; use pb.{call_b}
from_A
from_A                          # <- call_b(), defined in pb.spl, ran pa.spl's who()
```

Swapping the two `use` lines flips both to `from_B`. First-import-wins.

**2. The in-module call is NOT protected.** `call_b()` lives *inside* the module that
defines its own `who()`. It still reaches the other module's body. This directly
contradicts the resolution-policy comment that stood at
`src/compiler_rust/compiler/src/pipeline/module_loader.rs:1406-1411`, which claimed the
owner tag keeps `b.call_b()` reaching `b.who` "in either import order" — using this
exact `who()` example. That bullet has been retracted in-source with the measurement.

**3. Differing signatures collapse too, discarding arguments without an arity error.**
A's `shared_arity()` takes no parameters; B's takes one. B's own wrapper calls
`shared_arity(7)`:

```
PASS a_arity                    # A_arity0, correct
FAIL b_arity expected=B_arity1 actual=A_arity0
```

The argument `7` is silently dropped and the zero-parameter body runs. No type error,
no arity error, exit 0.

### Mechanism — the fix does not belong in `select_overload`

`FUNCTION_OVERLOADS` and `FUNCTION_MODULE_OWNER` are populated per-definition, and
`select_overload` (`interpreter_call/mod.rs:177`) already has an owner-tag tie-break.
**It is never reached.** Under `SIMPLE_DEBUG_OVERLOAD_SELECT=1` the probe emitted no
`[module-tie]` line at all, so by dispatch time `FUNCTION_OVERLOADS[name]` holds fewer
than two candidates.

Meanwhile `warn_duplicate_private_signatures` (`module_loader.rs:1519`) *does* see both
definitions in `module.items` and warns about them. So the second definition is lost
**between the flattening pass and interpreter registration**. Repairing the tie-break
cannot fix this; the registry must retain both definitions (owner-scoped keys, or
name mangling).

### Detection is inverted: the most dangerous shape is the quietest

Default run of the probe warned about `shared_arity` (differing signatures) only.
`_shared_helper` and `shared_public` — same-signature collisions that produced wrong
answers **in the very same run** — drew no warning, because that arm sits behind
`SIMPLE_DIAG_SAME_SIGNATURE_COLLISION`, default-off (`module_loader.rs:1509`). The
comment above that arm (`:1592-1607`) argues at length that the same-signature shape is
the one no other tool can detect, and then leaves it disabled. With the env var set the
warning fires correctly, so the detector works — only the default is wrong.

Flipping that default was deliberately NOT done in this lane: the repo-wide collision
census is large and a live bootstrap was running. It needs its own scoped change with a
measured noise count.

### Regression coverage added (currently RED by design — no fix landed)

- `test/01_unit/compiler/pipeline/fixtures/xmod_collision_a.spl`
- `test/01_unit/compiler/pipeline/fixtures/xmod_collision_b.spl`
- `test/01_unit/compiler/pipeline/fixtures/probe_xmod_collision.spl` — run-path probe,
  absolute-literal oracles, subprocess-driven. Current output:
  `PASS a_private / FAIL b_private / PASS a_public / FAIL b_public / PASS a_arity /
  FAIL b_arity` → `XMOD_COLLISION PROBE: FAILURES`
- `test/01_unit/compiler/pipeline/cross_module_symbol_collision_spec.spl` — reproducing
  spec, shells out under both `interpreter` and `jit`.
- `test/01_unit/compiler/pipeline/cross_module_collision_detection_spec.spl` — detection
  spec for the defect CLASS: every collision shape must be named on stderr under
  DEFAULT settings, and a wrong-answer collision must not be suppressible by an env var.

### Not proven in this lane

- Native (`compile --native`) behaviour was not re-measured; only interpreter and JIT.
- The exact pass that drops the second definition between flattening and registration
  was not isolated to a line.
- The noise cost of enabling `SIMPLE_DIAG_SAME_SIGNATURE_COLLISION` by default is
  unmeasured.

### Spec budget note + one assertion deliberately dropped

The first version of `cross_module_collision_detection_spec.spl` made THREE compiler
launches and timed out at the 900s test-daemon budget:

```
SPEC FILE VERDICT: ... executed=1 passed=0 failed=1 dropped=0 timeout=1
  reason=daemon-no-response budget_ms=900000
```

That is an UNVERIFIED result, not a red. The spec is now capped at one shell-out
launch per example (two total).

Dropping the third launch removed one assertion worth restoring when the budget
allows, recorded here so it is not silently lost:

> **A collision that produced a wrong answer must not be suppressible by an env var.**
> Running the probe with `SIMPLE_DIAG_SAME_SIGNATURE_COLLISION=0` should still report
> `_shared_helper`. Today it does not — the flag silences a warning about a
> demonstrably wrong result.

---

## CORRECTION 2026-08-17 (same lane, later the same session) — the defect is JIT-ONLY

**The section above overstated the defect, and this correction supersedes it on one
axis.** The claim that "the in-module call is NOT protected" and that the interpreter
is first-import-wins was produced by running `bin/simple run` **without pinning the
engine**. Plain `run` uses the **JIT**. With the engine pinned explicitly:

```
SIMPLE_EXECUTION_MODE=interpreter  ->  XMOD_COLLISION PROBE: ALL PASS
SIMPLE_EXECUTION_MODE=jit          ->  FAIL b_private / b_public / b_arity
```

Confirmed independently by the reproducing spec, whose two arms split cleanly:

```
cross-module same-name symbol collision
  PASS resolves each module's calls against its own definitions on the interpreter
  FAIL resolves each module's calls against its own definitions on the cranelift JIT
Results: 2 total, 1 passed, 1 failed
```

### What is true after the correction

- **Interpreter: CORRECT.** The owner-tag machinery
  (`FLATTEN_MODULE_OWNER_ATTR_PREFIX` / `FUNCTION_MODULE_OWNER` / `select_overload`)
  resolves in-module calls to the right module, for private names, public names, and
  differing arity alike. The long-standing source comment describing this was right;
  a retraction of it briefly written into `module_loader.rs` has been reverted.
- **JIT: WRONG, and broader than filed.** First-import-wins, including for a call made
  from *inside* a defining module — which the prior source comment covered only for the
  third-module caller. Not `_`-prefix specific. Not limited to identical signatures:
  `shared_arity(7)` reaches a zero-parameter body with the argument silently discarded
  and **no arity error**.
- **The `select_overload` "never reached" observation was measured on the JIT run** and
  says nothing about the interpreter path, which demonstrably works.

### Live collisions this run surfaced in the real tree

Running the spec printed the compiler's own warnings for genuine stdlib collisions,
including the one CRIT.md cited as corroboration:

```
public function `shell` has 3 co-compiled definitions with 2 differing signatures
  ((text)->ProcessResult vs (text)->ShellResult)
public function `dir_remove_all` ... ((text)->bool vs (text)->i32)
public function `file_read_bytes` ... ((text)->[i64] vs (text)->[u8])
public function `skip` ... (13-arg spec-DSL variant vs (text,text)->())
```

`file_read_bytes` returning `[i64]` under one definition and `[u8]` under the other is
a silent-wrong-result waiting to happen on the JIT lane specifically.

### Method note worth keeping

The wrong conclusion came from trusting the default engine. **Pin
`SIMPLE_EXECUTION_MODE` explicitly on every engine-sensitive measurement in this repo**
— the two engines disagree here, and "I ran `bin/simple run`" does not identify which
one answered.
