# Patchpoint and Signing Prerequisites for the Aspect/Dynload Lane (2026-08-19)

Scopes the two hardest blocked dependencies named in
`doc/05_design/language/aop/aspect_facet_dynload_smf_pack_design_2026-08-04.md`
(§14.1 `AdviceBindingRegistry`, §14.2 runtime state machine, §11.2
`SignatureTable`, §19 mission-critical profile) so a later session can decide
whether to build them. Design/research only; no source or test files were
edited.

## A. Backend join-point patchpoints

### What exists today (file:line)

Searched `src/compiler/70.backend/**`, `src/compiler/50.mir/**`, and the JIT
path (`src/compiler/95.interp/execution/*jit*`, `src/compiler/99.loader/*jit*`)
for `trampoline`, `patch`, `thunk`, `indirect.call|icall`, `relocat`,
`mprotect`, `PROT_EXEC`, `icache`.

**Nothing that binds live advice to a call site exists.** What does exist,
and is close enough to matter for cost estimation:

1. **Whole-module RW->patch->RX->icache-flush relocation, already working,
   general-purpose.** `src/compiler/99.loader/loader/module_loader.spl:400-421`
   (`moduleloader_apply_relocations`, called from module reload/hot-replace):
   for each loaded symbol it calls `native_make_rw(addr, size)`
   (:404), applies relocations via `apply_smf_relocations` (:412), then
   `native_make_executable(addr, size)` (:417) and
   `native_flush_icache(addr, size)` (:421). This is real, executed code, not
   a stub — it is how `moduleloader_reload`/hot-replace already works. The
   primitives it calls (`native_make_rw`, `native_make_executable`,
   `native_flush_icache`, `rt_mprotect`) live in
   `src/compiler/99.loader/loader/smf_mmap_native.spl:23-227` (also duplicated
   at `src/compiler/99.loader/smf_mmap_native.spl:37,133-197` and re-exported
   from `src/compiler/99.loader/__init__.spl:54,58`). A parallel, segment-level
   (not per-symbol) version exists at
   `src/compiler/99.loader/segment_mapper.spl:32-228`
   (`begin_relocation`/`end_relocation`, explicit W^X comment at :32-34).
   **This granularity is whole-symbol/whole-segment, not a single call-site
   instruction or NOP slot** — it re-protects and re-flushes the entire
   symbol's code range for any patch, which is correct but not what a
   per-call-site patchpoint needs for hot-path cost.
2. **Indirect-call codegen exists but only as an LLVM IR builder feature, not
   a patchable slot.** `src/compiler/70.backend/backend/llvm_ir_builder.spl:486`
   — "Emit indirect call through function pointer." This proves the backend
   *can* emit an indirect call, which is a necessary primitive for a
   patchpoint (patch the target pointer, not the instruction stream), but
   there is no call site marked as patchable, no reserved slot table, and no
   runtime-side API to look up/overwrite one.
3. **`trampoline`/`thunk` hits are all SFFI callback trampolines**
   (`src/compiler/70.backend/backend/callback_trampoline.spl:1-189`), which
   generate a fixed C trampoline function per SFFI callback *signature* at
   compile time. This is unrelated to advice binding — it never patches
   already-emitted code at runtime.
4. **Design doc itself says this does not exist.** Design line 14: "The
   current codebase already contains established `on pc{...} use ...` advice
   weaving and `dynsmf_*` startup manifests, but it does not yet provide" the
   dynamic-attach machinery. Design lines 838, 870, 960, 1174 all describe a
   "dormant patchpoint" / "joinpoint_slot_id" / weave-fingerprint schema that
   is **prose only** — `grep -rn "dynamic_joinpoint\|joinpoint_slot" src` (all
   of `src/`) returns zero hits. No `@dynamic_joinpoint` annotation, no
   join-point slot table, is implemented anywhere.

**Verdict: no patchpoint/trampoline-for-advice mechanism exists.** What
exists is a working, generic, whole-symbol runtime-code-rewrite primitive
(mprotect RW/RX + icache flush) that a patchpoint mechanism could be *built
on top of*, plus LLVM indirect-call codegen as a second usable primitive.
Building the join-point-specific layer is still fully unbuilt, but it is not
starting from zero — the two hardest low-level primitives (safe runtime code
rewrite, and indirect dispatch) are already proven in production code paths.

### Minimal interface to unblock the aspect lane

Scoped strictly to what `AdviceBindingRegistry` (§14.1) and the runtime state
machine (§14.2, `ChunksLoaded -> Relocated -> Bound -> Active`) need — not the
general "patchpoint framework" the design's Executive Decision gestures at.

1. **Backend emission side** (per function/site marked `@dynamic_joinpoint`,
   per design §6.12): at each eligible join point, instead of a direct call
   emit an **indirect call through a fixed, symbol-addressable slot cell**
   (a single 8-byte function-pointer slot, one per `joinpoint_slot_id`,
   grouped into a `JoinpointSlotTable` section analogous to the existing
   `ChunkEntry`/directory tables in §11.2). Default slot content: address of
   a no-op/pass-through stub. This reuses `llvm_ir_builder.spl:486`'s
   existing indirect-call emission — no new instruction-patching codegen is
   required, only slot-table bookkeeping in the MIR/backend layer that does
   not exist today.
2. **Loader/runtime side**: `AdviceBindingRegistry` binds a
   `joinpoint_slot_id -> advice chain entry pointer`, then overwrites the slot
   cell using the existing `native_make_rw` -> write 8 bytes ->
   `native_make_executable` -> `native_flush_icache` sequence
   (`smf_mmap_native.spl`), i.e. writing to **a data slot**, not into the
   instruction stream — this sidesteps re-protecting and reflushing an entire
   code symbol per bind/unbind, which the current whole-symbol
   `moduleloader_apply_relocations` path would otherwise force. This is the
   one piece of new runtime code actually needed: a slot-cell version of the
   relocation-apply primitive, operating on a single pointer-sized cell
   instead of `loaded_sym.size` bytes.
3. **Safety constraints, already established precedent to follow, not new
   design**:
   - W^X: `smf_mmap_native.spl:137-138` states the existing rule — map RW
     only, grant X later via `native_make_executable`. A slot-cell write must
     do the same: RW the containing page, write the pointer, RX it back. On
     platforms without page-level slot isolation this still forces a
     page-granularity re-protect, which the design should account for as a
     per-bind cost, not assume away.
   - icache flush: `native_flush_icache` (`smf_mmap_native.spl:187`) is
     required after any code-adjacent write on non-x86 (weak memory-ordering
     ISAs need it even for a same-cache-line pointer update visible to
     speculative/prefetched instruction fetch); the existing call sites
     already do this unconditionally and the slot mechanism should too.
   - Concurrency: §14.6's "single activation future/state per aspect
     generation" must extend to slot writes — a torn 8-byte pointer write is
     the standard atomicity requirement; on all currently-targeted backends a
     naturally-aligned 8-byte store is atomic, but this must be asserted, not
     assumed, in the slot table's alignment contract.

### Blast radius

Backend: new slot-table section format + MIR marking pass for
`@dynamic_joinpoint` sites (§6.12) — moderate, additive, does not touch
existing codegen for unmarked functions (§20.2's "static omitted aspect"
byte-identical guarantee is preserved because nothing changes for
undecorated code). Loader: one new primitive (slot-cell RW/write/RX/flush),
reusing existing mprotect/icache plumbing — small. Runtime: new
`AdviceBindingRegistry` + state machine (§14.1/14.2) — this is the actual
bulk of the work and was never in scope of "patchpoints" per se.

### Recommendation: BUILD-NOW (narrowly scoped)

The two hard primitives (safe runtime code/data rewrite with correct W^X and
icache handling; indirect dispatch) already exist and are exercised in
production paths (`module_loader.spl`, `llvm_ir_builder.spl`). The remaining
work is a bounded, mechanical extension (slot table + single-cell patch
primitive), not new systems research. This is *lower* risk than the design
doc's tone implies, provided the scope is held to the slot-cell design above
and not expanded to general inline-code patching (self-modifying instruction
streams), which is genuinely unbuilt and should stay DO-NOT-BUILD-YET.

## B. Signing authority

### What exists today (file:line)

Searched `src/lib/common/crypto/**` for sha256, ed25519, x509, pem, and any
verify/sign entry points.

1. **A complete, self-tested pure-Simple Ed25519 implementation exists.**
   `src/lib/common/crypto/ed25519.spl`: `pure_ed25519_sign` (:1318),
   `pure_ed25519_verify` (:1380), `ed25519_pubkey`/keypair derivation (:1292,
   1307), plus a runnable self-test with real test vectors, including a
   negative case (corrupted signature must be rejected) at :1477-1487 and
   :1519-1524. This is not a stub — it is field arithmetic through to
   full sign/verify with test-vector coverage.
2. **SHA-256, SHA-512, SHA-3, BLAKE2/3, HMAC, HKDF, PBKDF2, Argon2, X25519,
   ECDSA-P256, RSA-PKCS1, AES-GCM, ChaCha20-Poly1305, ML-KEM (x25519_mlkem768
   hybrid), X.509 DER parsing (`x509.spl`), and PEM parsing (`pem.spl`) all
   exist** as siblings in `src/lib/common/crypto/`. Ed25519 verification
   itself is already consumed by TLS certificate and SSH auth code
   (`src/lib/nogc_sync_mut/tls/certificate.spl`,
   `src/os/apps/ssh_client/ssh_client_auth.spl`,
   `src/lib/nogc_sync_mut/io/signature_sffi.spl`), so the primitive is proven
   in real call paths, not just unit-tested in isolation.
3. **Nothing wires any of this to aspect packs.** `grep` for
   `SignatureTable`/`E-APACK003`/"sign.*verif" across `doc/05_design/language/aop`
   returns only the design doc's own prose (lines 910, 988, 1519) — no
   implementation reference. There is no build-time signer, no trusted-key
   store, no `aspect_pack.spl` call into `ed25519.spl`. Confirmed by reading
   `src/lib/common/aspect_pack.spl`'s header (catalog/pack format description,
   lines 1-60): it defines CRC32 integrity checks per module/catalog entry
   but never mentions signatures — CRC32 detects corruption, not tampering.
4. **No key-management doc or convention exists.**
   `grep -rli "signing.key|private.key.*build|build.time.*sign" doc/04_architecture
   doc/05_design` found no aspect/build-signing convention (the two hits,
   `security_convention_first_architecture.md` and `simple_process_manager.md`,
   are unrelated general security docs, not a signing-key story).

**Verdict: the cryptographic primitive (Ed25519 sign/verify) is real,
complete, and already proven elsewhere in the tree. The missing piece is
100% key-management and process, not cryptography.**

### What a real chain requires

- **Who signs**: the build pipeline that produces a released aspect-pack SMF
  (`src/compiler/80.driver` output stage) — not a developer's personal key,
  not the loader. Signing must be a distinct, auditable build step so a
  compromised dev machine cannot forge a pack that the runtime will accept.
- **When**: at pack-finalization time, after the `AspectPackDirectory`
  (§11.2: header, `AspectEntry[]`, `ModuleEntry[]`, ..., `ChunkEntry[]`,
  `MinimalStringTable`) is fully assembled and its bytes are frozen — the
  signature covers the directory bytes (or a hash of them), matching how
  `pure_ed25519_verify(public_key, message, signature)` already expects a
  message + detached signature.
- **Where the key lives**: the signing (private) key must never be readable
  by the runtime/loader — build-side only, e.g. an HSM, CI secret store, or
  offline key ceremony. The runtime only ever needs the **public** key(s),
  embedded or provisioned via a trusted root (analogous to how
  `x509.spl`/`pem.spl` already model certificate trust chains for TLS — the
  same trust-root pattern applies here: either a single pinned public key per
  deployment, or a small root-of-trust list with revocation).
- **What the verifier checks**: `pure_ed25519_verify(public_key, catalog_or_pack_bytes_hash, signature)`
  against the pack's `SignatureTable` entry, gating the `Resolving ->
  ChunksLoaded` transition in §14.2's state machine — i.e., verification must
  happen *before* any chunk is decompressed or mapped executable, matching
  §14.3 step "verify index hash/signature" (already specified, just
  unimplemented) and matching E-APACK003's existing error code for exactly
  this failure.
- **Failure mode**: fail-closed, matching this codebase's stated convention
  elsewhere (CLAUDE.md pattern, and E-APACK003's existing slot in the design
  doc's diagnostic table) — a verification failure must produce a typed error
  and block load, never a silent fallback to unsigned load. Under §19's
  mission-critical profile (`signed_pack: require`), a verification failure
  at startup must prevent application publication entirely (§19's own stated
  rule: "A failed aspect load prevents application publication").

### Recommendation: DO-NOT-BUILD-YET

Implementing the `SignatureTable` check today, with no key-management story,
would let CI generate an ephemeral throwaway keypair, sign with it, and
verify with the matching public key baked into the same commit — which
**verifies successfully against nothing meaningful**: anyone who can edit the
repo can regenerate both halves and produce a "valid" signature over a
tampered pack. That is decoration, not security, and is explicitly why the
task framed it this way. The cryptographic primitive is not the blocker and
does not need building — `ed25519.spl` is ready to call today. What is
missing and must be decided by a later session first: **who controls the
signing key, where it is stored, and how the runtime's trusted public key
set is provisioned and rotated** (this is a process/infra decision, not a
code change). Until that exists, do not wire `pure_ed25519_verify` into the
loader — doing so would create a false sense of integrity guarantee ahead of
the actual guarantee.
