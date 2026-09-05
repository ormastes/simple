# priority_bug.md — 33 dangerous rows handed to a second host

**Derived 2026-08-17.** Fourth companion to the three handoff docs. Read those
first; this one does not repeat them:

- `offhost_bug_assignment_2026-08-17.md` — *where* work can happen (582 portable
  / 449 no-build / 42 mac-gated) and the **hash-partition claim protocol**, which
  this document reuses verbatim rather than inventing a second scheme.
- `p1_non_bootstrap_bugfix.md` — the 240 P1s off the bootstrap critical path.
- `p2_p3_bugfix.md` — the 980 P2/P3 bulk.

Those three answer *what is available*. This one answers a narrower, sharper
question: **of the available rows, which ones are actively dangerous, and which of
those is nobody working on right now?** It is a priority overlay on the same
corpus, not a new corpus. Every row here is also a row in `portable.tsv`.

## What "dangerous" means here

Not "inconvenient", not "loud". **Dangerous = produces a wrong answer without
saying so, or breaks a security/correctness boundary.** A crash is safe by
comparison: it tells you. Selection was scored on four shapes, in priority order.

### 1. Silent-wrong-result generators

The core class. Confirmed live examples measured on this host today, given as
calibration for what the shape looks like in the wild:

- A **nonexistent** method `ByteSpan.at(0)` returns `3` instead of erroring. **A
  missing method that ANSWERS instead of failing is the worst shape in this
  entire corpus** — it converts a typo into silently plausible data, and no test
  that trusts the return value can ever detect it.
- `Result<u8>.unwrap_or` returns `1776` = `222 << 3` — the boxing shift is never
  undone. `Result<i64>` on the same path is correct, so the defect is invisible
  unless you happen to test the narrow width.
- `1 + 2.5` under JIT prints `4615063718147915776` — the raw f64 bit pattern.
- JIT **cross-module function-name misresolution**: a module-local call resolves
  to a different module's same-named function. Nothing warns.

### 2. Security / crypto correctness

~33 security-flavoured rows exist in the corpus; the strongest are below. The
pattern to hunt was resolved today in `paseto.spl:103`: `_p4_b64u_decode`
declared `idx3` inside the `i+2` branch and read it in the `i+3` branch, dropping
the third byte of **every** quad. The consequence is the important part — the
corrupted input made the **BLAKE2b tag comparison VACUOUS**, not merely wrong. A
verification that cannot fail is worse than one that fails. **Look specifically
for corrupted-input-makes-verification-trivially-pass, not for "crypto output
looks wrong".**

### 3. Fail-open guards and unregistered externs

Highest yield per hour of anything in this set. `smf_reader.spl` declared six
`rt_smf_reader_*` externs with **no implementation anywhere**; an unregistered
extern yields `0`/`nil`, so `open()` returned `Ok` for **any** input, including
non-SMF junk (fixed at `0171d5b2510`). Fixing it then exposed three further
defects the fail-open had masked — including a call to `s.is_exported()`, a
method that **does not exist** on `SmfSymbol`, which had never been a compile
error because the loop body never executed. One fix, four defects.

### 4. Engine-divergence rows where the JIT/native side is wrong

**Read this before touching any divergence row.** At least **four rows in this
corpus are filed against the WRONG ENGINE**: the prose blames the interpreter,
but the interpreter is CORRECT and the JIT/seed is wrong. Two in this very set
say so in their own status lines —
`seed_jit_me_method_array_of_struct_writeback_nil_receiver_2026-07-23.md`
("interpreter correct") and `jit_hex_to_u8_array_byte_corruption_2026-06-30.md`
("interpreter is correct"). **Do not start by instrumenting the interpreter.**
Establish which engine is wrong *first*, with a two-engine subprocess comparison,
before forming any hypothesis about a cause.

## Scoring, stated so it can be re-derived

Mechanical, from `scratchpad/triage/portable.tsv`:

```
score = 2 * (#silent-wrong keywords) + 3 * (#security keywords) + 4 * (severity == P1)
```

Silent-wrong keywords: `silent(ly)`, `wrong`, `incorrect`, `corrupt`, `vacuous`,
`fail-open`, `always true`, `always return`, `returns 0/zero`, `no-op`,
`misleading`, `false success`, `false green`, `unregistered`, `undeclared`,
`never implemented`, `stub`, `truncat`, `off-by`, `misresolv`, `boxing`, `shift`,
`tag`, `garbage`, `bit pattern`, `unvalidated`, `bypass`, `nonexistent`, `does
not exist`, `swallow`, `uninitialis/zed`.
Security keywords: `crypto`, `aes`, `sha*`, `hmac`, `blake`, `paseto`, `jwt`,
`tls`, `ssl`, `cert`, `signature`, `verif`, `auth`, `token`, `nonce`, `random`,
`seed`, `permission`, `sandbox`, `escape`, `injection`, `traversal`, `secret`,
`key`, `cipher`, `mac`, `digest`, `password`.

65 rows scored >= 8 after exclusions. **The 40 highest were selected; 7 were dropped at push time because
origin moved them under a concurrent lane (see below), leaving 33 handed off.**
The remaining rows stay unclaimed and available to anyone.

## What is EXCLUDED, and why

- **Bootstrap-critical (66 rows).** They need this host's live stage-2/3 build,
  which cannot be shipped. And the build itself is currently broken in a way that
  makes it useless as a verification substrate: **`stage3` dies of SIGSEGV (exit
  139) at a nondeterministic point** — 576 files in one cycle, **1 file in the
  next with frozen source** — and the crash **vanishes under gdb's disabled
  ASLR**. That signature is a **wild / uninitialised pointer**, not a source-level
  logic bug. Handing that off would hand off an unreproducible environment.
- **Anything already ACTIVE.** Verified three ways, unioned: `state_*.md` session
  files under the scratchpad (56 rows named), the 16 panes of tmux `24:0` read by
  **scrollback content, not pane order** (17 rows named), and `git log --since='6
  hours ago'` restricted to commits touching **<= 6 bug docs** (221 rows). The
  <= 6 restriction matters: the bulk triage sweeps today touched 1,305 bug docs in
  single commits, and counting those as "active" would have excluded the entire
  corpus. Focused commits mean real per-row work; sweeps do not.
- **The ~61 enterprise / `.spipe` rows.** Owned by the enterprise lane
  (`state_w23-enterprise.md`, `state_ent-fanout.md`, `state_enterprise-suite.md`).
- **7 further rows dropped at push time.** Rebasing onto the moving `origin/main`
  conflicted on them, which is direct evidence another lane is editing them right
  now — the strongest possible ACTIVE signal, stronger than any of the three
  detectors above. They were released rather than fenced.
- Rows whose own status line already says "FIXED" or "source fixed" — two were
  dropped and replaced, because they are retirement paperwork, not danger.

## The fence — CLAIMED-OFFHOST

**Convention.** Every row handed off carries, near the top of its bug doc, exactly
one line:

```
> **CLAIMED-OFFHOST 2026-08-17** — do not work locally; assigned to a second host. See doc/03_plan/infra/priority_bug.md
```

**Rules.**

1. A local agent that opens a bug doc and sees that line **stops** and picks
   something else. No exceptions, no "I'll just take a quick look" — a local
   partial fix is what makes the remote host's ablation proof impossible.
2. The marker is the authority, not this document's table. If the two disagree,
   the in-doc marker wins.
3. Only the off-host owner removes it, and only in the same commit that retires
   or fixes the row.
4. The marker is **not** a claim on the surrounding source file. Another lane may
   legitimately edit `method_calls_literals.spl` for a different row; the fence is
   per-row, not per-file.

## The 33 handed-off rows

`score` is the danger score above; higher is more dangerous.

| score | sev | bug doc | title | primary file |
|---|---|---|---|---|
| 19 | P1 | `cert_chain_signature_verification_missing_2026-07-17.md` | TLS chain-of-trust verify_signature has no implementation, so cert chains are never crypto | `src/lib/nogc_sync_mut/tls/validation.spl` |
| 15 | P1 | `ed25519_rfc8032_t_sha_abc_pubkey_mismatch_2026-07-20.md` | RFC8032 7.1 T_SHA_ABC vector: ed25519 derives the wrong public key and verify fails | `src/os/crypto/ed25519_ops.spl` |
| 14 | P2 | `crypto_reference_signature_key_ops_unresolvable_2026-07-20.md` | std.signature.key_ops has no .spl source; whole spec cannot load | `test/01_unit/lib/crypto/crypto_reference_spec.spl` |
| 14 | P1 | `set_method_route_dict_returns_nil_array_tuple_silent_noop_2026-08-02.md` | dict .set() returns nil under the seed JIT while the mutation lands; array/tuple .set | `src/compiler/50.mir/_MirLoweringExpr/method_calls_literals.spl` |
| 14 | P1 | `p256_stack_imports_nonexistent_fe_p256_module_2026-08-04.md` | p256.spl imports std.common.math.field.fe_p256 which does not exist; P-256 unloadable | `src/os/crypto/p256.spl` |
| 14 | P1 | `duplicate_public_symbols_differing_return_types_jit_misdispatch_2026-08-09.md` | 373 co-compiled symbol collisions per spec run; identical-signature ones silently vacate | `src/compiler/10.frontend/core/interpreter/eval_tables.spl` |
| 13 | P2 | `crypto_sffi_random_hex_degrades_to_empty_string_on_entropy_failure_2026-08-08.md` | random_hex degrades to empty string on CSPRNG failure; random_salt inherits it | `src/lib/nogc_sync_mut/io/crypto_sffi.spl` |
| 13 | P1 | `enum_bare_name_collision_registry_2026-08-01.md` | Bare enum-name registry keys make a match arm silently select the wrong cross-module enum | `src/compiler/10.frontend/core/types.spl` |
| 13 | P1 | `ecdsa_p256_sign_verify_roundtrip_broken_2026-07-20.md` | ECDSA P-256 verify rejects a 64-byte signature this repo's own sign just produced | `src/lib/common/crypto/ecdsa_p256.spl` |
| 13 | P1 | `ecc_p384_p521_sign_verify_broken_2026-07-20.md` | ECDSA P-384 sign returns a 0-byte signature and NIST CAVP verify fails on P-384 and P-521 | `src/lib/nogc_sync_mut/io/signature_sffi.spl` |
| 12 | P2 | `tls_signature_positive_verification_blockers_2026-06-06.md` | TLS signature verification has no positive test: ed25519/RSA-PSS/cert-chain specs cannot | `test/03_system/os/os_tls_cert_chain_spec.spl` |
| 12 | P2 | `artifact_manifest_signature_verification_no_trust_anchor_2026-08-07.md` | SimpleArtifactManifest.signature has no trust-anchor or key-distribution infra | `src/os/kernel/loader/artifact_manifest.spl` |
| 12 | P2 | `aes_utilities_unseeded_key_iv_nonce_generators_are_lcg_constants_2026-08-08.md` | generate_aes_key/generate_iv/generate_nonce are constant-seeded LCGs | `src/lib/common/aes/utilities.spl` |
| 12 | P1 | `salsa20_xsalsa20_keystream_kat_mismatch_2026-07-20.md` | Salsa20/XSalsa20 keystream does not match the DJB/NaCl/libsodium published KAT vectors | `src/os/crypto/salsa20.spl` |
| 12 | P1 | `module_global_write_lost_on_frame_pop_2026-07-28.md` | Module-level var write is silently reverted on frame pop in the interpreted lane, inverting safety flags | `src/compiler/10.frontend/core/parser.spl` |
| 12 | P1 | `interp_expect_to_equal_swallows_failures_multi_describe_2026-06-15.md` | expect().to_equal() swallows failures in specs with multiple describe blocks | `src/lib/nogc_sync_mut/spec.spl` |
| 12 | P1 | `curve448_x448_scalarmult_kat_mismatch_2026-07-20.md` | Curve448/X448 scalar-mult and ECDH mismatch every RFC 7748 KAT vector | `src/lib/common/crypto/typed/ctypes.spl` |
| 10 | P2 | `native_module_i32_derived_constant_tag_shift_2026-07-27.md` | Module-level derived i32 constant reads tag-shifted under native codegen | `src/compiler/70.backend/backend/_MirToLlvm/core_codegen.spl` |
| 10 | P1 | `seed_jit_me_method_array_of_struct_writeback_nil_receiver_2026-07-23.md` | me-method write-back into a self array-of-structs field aborts with field access on nil | `src/lib/hardware/link_mux/mux.spl` |
| 10 | P1 | `parser_bare_trailing_neg_literal_folds_prev_line_2026-07-27.md` | A bare trailing `-1` return line folds into the previous line, silently wrong value | `src/lib/common/config_core/layers.spl` |
| 10 | P1 | `native_try_op_on_option_silent_wrong_2026-07-14.md` | ? applied to an Option inside a Result-returning fn silently miscompiles (rc 208 vs 209) | `src/compiler/50.mir/_MirLoweringExpr/switch_operators_calls.spl` |
| 10 | P1 | `native_nil_receiver_crossmodule_method_scalar_return_2026-07-27.md` | Cranelift AOT mis-tags a cross-module struct method's scalar return: x as i64 yields 0 | `src/runtime/runtime_native.c` |
| 10 | P1 | `native_nested_struct_value_copy_alias_2026-07-17.md` | Native nested struct value copies retain aliases so writes leak into the source struct | `src/compiler/50.mir/_MirLowering/function_lowering.spl` |
| 10 | P1 | `me_method_mutation_through_optional_binding_discarded_2026-08-04.md` | `me`-method mutation through an Option-typed binding is silently discarded (exit 0, no warning) | `src/compiler/50.mir/_MirLoweringExpr/method_calls_literals.spl` |
| 10 | P1 | `indexed_char_to_i64_silent_zero_family_2026-08-10.md` | s[i].to_i64() on a string-indexed char silently returns 0 instead of the char code | `src/lib/nogc_sync_mut/http_server/h2_server.spl` |
| 10 | P1 | `enum_pattern_match_optional_value_silent_fallthrough_2026-07-20.md` | match on a T? enum silently falls through to _ for every field-binding variant arm | `src/app/ui.browser/event_bridge.spl` |
| 10 | P1 | `ed25519_scalar_mul_ct_regression_2026-07-20.md` | ed_scalar_mul_basepoint delegates to _simple which branches on each secret scalar bit | `src/os/crypto/ed25519_ops.spl` |
| 10 | P1 | `dotq_existence_check_is_scalar_truthiness_on_jit_2026-07-27.md` | .? lowers to a raw scalar truthiness test on JIT/native so 0.? is false and "".? is true | `src/compiler/50.mir/_MirLoweringExpr/method_calls_literals.spl` |
| 10 | P1 | `chained_static_ctor_receiver_drops_mutation_2026-08-01.md` | A mutating method chained directly off a static constructor call is a silent no-op | `src/compiler/10.frontend/core/interpreter/eval.spl` |
| 10 | P1 | `aliased_array_mut_param_mutation_lost_interpreter_2026-08-06.md` | Array passed as both mut and non-mut param silently discards the mutation | `src/compiler/10.frontend/core/interpreter/_EvalOps/call_method_eval.spl` |
| 9 | P1 | `simpleos_optimizer_loses_alias_key_array_2026-07-13.md` | Optimizer passes tagged nil as local_ids so local_count_index faults loading array length | `src/compiler/70.backend/backend/native/isel_x86_64.spl` |
| 9 | P1 | `jit_hex_to_u8_array_byte_corruption_2026-06-30.md` | JIT corrupts [u8] built via ((hi<<4)|lo).to_u8() loop; interpreter is correct | `src/lib/common/cert/x509_typed.spl` |
| 9 | P1 | `interpreter_bare_arg_not_some_wrapped_at_optional_param_2026-08-04.md` | Bare arg at a T? param is not Some-wrapped so case Some(x) matches no arm (silent fall-through) | `src/compiler/10.frontend/core/interpreter/eval.spl` |

### Shape of the set

- **13 rows are crypto / security boundary**: TLS chain-of-trust verification
  with **no implementation at all**, ed25519 wrong public key + a
  constant-time regression, ECDSA P-256 rejecting its own signatures, P-384
  returning a **0-byte** signature, Salsa20/XSalsa20 and X448 failing every
  published KAT, `random_hex` **degrading to an empty string** on CSPRNG failure,
  AES key/IV/nonce generators that are **constant-seeded LCGs**, and an artifact
  manifest whose signature has no trust anchor. Several of these are the
  vacuous-verification shape described above, not merely wrong output.
- **~20 rows are silent-wrong-result** in the compiler: `dict .has()` answering
  false for a key that is present, `.set()` returning nil while the mutation
  lands, a bare identifier in `case`/`match` position becoming an **irrefutable
  binding** that swallows every later arm, `?` on an `Option` miscompiling,
  mutations discarded through optional bindings and aliased `mut` params, `.?`
  degrading to raw scalar truthiness so `0.?` is false and `""​.?` is true.
- **1 row is the fail-open shape directly**:
  `mir_unresolved_method_const0_fails_open_2026-07-28.md` — an unresolved method
  call lowers to `emit_const(temp, Int(0))` while **sibling sites in the same file
  fail CLOSED via `rt_panic`**. Read that dispatch table; the asymmetry is the
  bug, and it is the same asymmetry as the Dict/Array split below.
- **2 rows are the wrong-engine trap** flagged in section 4.

## What the other host needs to be effective

This section is the point of the document. The rows are the easy part.

### ~29-37% of any row set is ALREADY FIXED but mislabelled

"**Did not reproduce — here is the symbol/commit in current source**" is a
**SUCCESS** that retires the row, not a failure to do the work. Budget for it: it
is roughly one row in three, and it is the cheapest hour available.

**Classify by CONTENT, never by SHA ancestry.** Constant rebasing rewrites SHAs
here, so a commit can be unreachable from `origin/main` while its content is
present in the tree. Grep for the fix in current source.

**Treat the stamp "re-verified by source inspection" as ABSENT.** It was proven
wrong on **37%** of the rows it appears on. It carries no information. Re-verify.

### Five false-signal generators measured today

Each of these manufactures a phantom bug. All five were observed, not theorised.

| # | generator | what it fakes | the discipline |
|---|---|---|---|
| a | **`bin/simple` is a stale Rust seed** (mtime 2026-08-16 22:59) | wrong root causes — **three** today came from trusting it | check `bin/simple --version`; know which binary produced every result |
| b | **`earlyoom --prefer ^(simple\|...) --avoid ^(claude\|...)`** SIGTERMs the compiler | a spec that was killed looks like a spec that failed | **`rc=143`/`144` with no `Results:` line is UNVERIFIED, never FAILED.** Re-run it |
| c | **wedged session daemon** | a **security-shaped false RED** that needed **three retractions** | always pass `--no-session-daemon` |
| d | **`test` is the tree-walk interpreter; `run` is the Cranelift JIT** | a JIT defect that "does not reproduce" | **a spec body CANNOT exercise a JIT defect.** Shell out to a subprocess and compare engines |
| e | **`scripts/resource/test-slot.shs` does not propagate env vars to the child** | a **false green control** — your negative control never had the variable set | use `env VAR=1 bin/simple ...` directly |

### Never accept exit 0 as a pass

Require an explicit `Results:` line in the output. A runner today printed **~1897
warning lines with zero result lines and exited 0**. Exit 0 means the process
ended, nothing more. And never read an exit code through a pipe — `cmd | tail`
gives you *tail's* status; assign `rc` on the following line.

### Prove causation by ABLATION

Apply the fix, verify green, then **REMOVE the fix and confirm it goes red again**.
Without the removal step you have proven nothing. Today:

- one "fix" turned out to be **unreachable code** — it could not have had any
  effect, and the green was somebody else's change;
- one verifier declared a fix **unnecessary** because it probed a tree that
  **already contained the fix**.

Both would have been caught in seconds by ablation.

### Collapse families BEFORE patching

Two families in this corpus, and both punish symptom-driven work:

- **61-bit boxed-int truncation** — values are stored `v << 3` with a 3-bit tag,
  so any `|v| >= 2^60` silently loses its top bits. This spans **~10 separate bug
  docs**. Fix the representation once; retire ten rows.
- **Guarded builtin-name dispatch** — has a **Dict half** (silent-wrong, already
  fixed) and an **Array half** (loud PANIC, still open). They fail
  **DIFFERENTLY**, so **symptom clustering will not find the rest of this
  family**. The only way to enumerate it is to read the dispatch table itself and
  check every entry's failure mode. `mir_unresolved_method_const0_fails_open`
  above is the same asymmetry in a third place.

### Two specs per fix

A **reproducing** spec (red before, green after) **and** a **similar-problem
detection** spec that generalizes to the defect **class**. The detection spec
caught a gap its own reproducer missed **six separate times** today — including
one case where the reproducer still passed with the fix removed.

### Claim and push protocol

- **Claim by hash partition**, exactly as documented in
  `offhost_bug_assignment_2026-08-17.md` ("How a second PC picks work without
  collision"). Do not invent a second scheme. `$1` is the bug doc filename, which
  is stable, so the same row always lands on the same machine and two machines
  with different `n` can never collide.
- **Push to a branch per machine — never straight to `main`.** This host has ~20
  lanes committing concurrently and has already suffered a silent revert.
- Use `--timeout <n>`, not `SIMPLE_TIMEOUT_SECONDS` (still misbehaves).
- Embedded fixture sources inside specs must avoid `{...}` entirely — the *spec's*
  lexer resolves the interpolation, not the fixture's, and the file dies with
  `zero-examples` before any example runs.

## Deliverable per row

1. The reproduce-first evidence, quoting the `Results:` line — or the
   did-not-reproduce evidence naming the symbol in current source.
2. The two specs.
3. The ablation transcript.
4. Removal of the `CLAIMED-OFFHOST` marker in the same commit.
