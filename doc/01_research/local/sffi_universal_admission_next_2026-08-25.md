<!-- codex-research -->
# SFFI universal admission: next local research checkpoint

**Date:** 2026-08-25  
**Tree:** `fbde06072d5`
**Scope:** owned `src/compiler`, `src/compiler_rust`, `src/lib`, `src/os`, and
SFFI audit tooling; vendor trees excluded.

## Verdict

Simple SFFI is **not globally safe, verified, or signed**. The repository has
useful fail-closed pieces, but no current evidence proves universal production
admission across interpreter, JIT, native, dynload, and SimpleOS.

## Bootstrap sandbox authority checkpoint — 2026-08-26

The bootstrap sandbox builder exposed 22 untagged raw declarations. Seven were
unused query/cleanup/overlay declarations and have been removed. Each of the 15
live reset/configure/apply calls is now explicitly declared FFI-unsafe and
confined to its own smallest lexical `unsafe(ffi)` expression. The existing
final `rt_sandbox_apply() -> bool` remains the transaction admission check, so
provider failure is still returned as `Err` rather than a successful sandbox.
The exported `apply_sandbox` operation is itself explicitly unsafe because a
boolean cannot prove rollback, unwind safety, or exact provider identity for an
irreversible process-global policy change.

The direct topology is unchanged: one reset, at most one scalar mutation per
selected limit, one mutation per domain/path, and one apply. No lookup, hash,
signature operation, wrapper frame, retry, allocation, copy, lock, or loop was
added. The Rust provider and interpreter registrations exist for all 15 live
symbols. Exact typed-native `RuntimeFuncSpec` entries do not exist, however, so
prefix tier classification must not be mistaken for ABI verification. Exact
artifact identity, trusted signature, and proof receipts also remain absent.
The source-ledger delta is therefore 7 fewer declaration rows, 15 newly tagged
and contract-documented rows, and zero newly signed/admitted symbols; a future
full census must measure the new workspace totals.

## Bootstrap atomic stop-the-line checkpoint — 2026-08-26

The next untouched family was not mass-tagged. Static comparison of
`compiler_rust/lib/std/src/infra/atomic.spl`, the exact native registry, the
interpreter registrations, and the Rust provider found argument-count and
boolean ABI mismatches, fabricated compare-exchange decoding, mutating flag
inspection, a missing spin-loop closure, and a mutex/map implementation exposed
as “lock-free.” The exact evidence and semantics-preserving repair order are in
`doc/08_tracking/bug/bootstrap_atomic_sffi_abi_and_semantics_2026-08-26.md`.
At that checkpoint the boundary remained unsafe and untouched pending an ABI
fix; annotations were not allowed to hide a hot-path mis-call.

Follow-up: the source ABI repair is now implemented. All 23 bootstrap atomic
declarations are explicitly unsafe, advisory ordering no longer crosses the
SeqCst provider ABI, compare-exchange is a real one-call boolean operation, and
flag observation is a real one-call non-mutating load. C, Rust, interpreter,
and native registry closure now includes boolean CAS, flag load, and spin hint.
Construction adds only a failure-path handle comparison; ordinary operations
retain exactly one provider call and remove ordering conversion work. The Rust
compatibility provider remains mutex/map-backed and all artifacts remain
unsigned/unadmitted, so this is source repair rather than verification.

## SimpleOS tools-test authority checkpoint

`src/os/tools_test.spl` had sixty ambient calls to its one serial-output
interface.  The declaration is now explicitly tagged and every call routes
through one mandatory-inline `ffi` owner.  The focused
`os-tools-test-sffi-authority.shs` ratchet passed and pins both hosted and
freestanding runtime providers.

Review found a direct fabricated-test-success defect: `test_run(code, name)`
ignored every tool exit code and always invoked `test_ok`.  It now records PASS
only for zero and records a named FAIL containing the nonzero exit code
otherwise.  Successful runs retain the same tool invocation, one result line,
counter update, allocation behavior, and O(1) harness work.  No lookup, lock,
hash, signature operation, or generic dispatch was added.

The authoritative call census changed as follows:

- raw call sites: 19,211 -> 19,152
- lexical unsafe: 3,256 -> 3,257
- function unsafe: unchanged at 919
- missing authority: 15,036 -> 14,976

The file now reports one raw row, lexically authorized, and zero missing
authority.  This fixes the false-pass harness but does not cryptographically
verify the invoked tools or runtime artifact; verified-and-signed admission
remains 0.

## CUDA raw-wrapper unsafe-surface checkpoint

The compiler CUDA facade exposes raw integer device/context/module/function
handles, host/device pointers, byte extents, and overloaded status/handle
results.  Without typed resources, lifetime validation, or exact provider
evidence, none of its Tier-2 wrappers can honestly be a safe API.  All 21 raw
declarations and all 21 smallest wrappers are now explicitly `unsafe(ffi)`.

Each wrapper still invokes its raw CUDA ABI directly once.  No extra owner,
branch, allocation, copy, synchronization, lookup, hash, lock, loop, or generic
dispatch was added.  Existing semantic status integers and device-count/name
types were preserved rather than converted to booleans or fabricated defaults.

Provider coverage remains split:

- typed native and interpreter: 13 symbols
- typed native only: 1 symbol
- interpreter only: 7 symbols
- neither: 0 symbols

The focused unsafe-surface ratchet passed.  The authoritative census changed:

- raw call sites: unchanged at 18,875
- missing authority: 14,598 -> 14,577
- lexical unsafe: unchanged at 3,320
- function unsafe: 957 -> 978

No production self-hosted optimizer or CUDA benchmark was available.  Provider
parity, typed ownership, bounds, exact artifact identity, signatures, and
evidence admission remain absent, so CUDA and the wider SFFI estate are not
globally verified or signed; verified-and-signed admission remains 0.

## Curve25519 small-limb hot-path authority checkpoint

`src/os/crypto/curve25519_smalllimb.spl` contained 26 unconditional foreign
serial writes in its scalar-multiplication path plus nine calls to a no-op
debug helper. These were stray diagnostics, not protocol receipts. Both sets
were removed, eliminating their I/O/call overhead and the serial SFFI family
without changing arithmetic or returned data.

The remaining `rt_bytes_u8_at` declaration and direct owner are explicitly
unsafe. The load/decode/clamp/mask helpers and public entry/probe functions
propagate that authority because they require exact 32-byte scalar or
u-coordinate extents. No per-byte bounds branch or fabricated zero is added.

The focused authority/provider/performance ratchet passed. It preserves the
fixed 255-step ladder (`bit_pos = 254` through zero), radix-2^25/2^26 masks,
carry flow, and `a24 = 121665` operation. The byte accessor appears in both
typed registries. The census changed as follows:

- raw call sites: 18,770 -> 18,744
- missing authority: 13,975 -> 13,948
- lexical unsafe: unchanged at 3,406
- function unsafe: 1,389 -> 1,390

Exact input types, bounds proof, constant-time verification, exact artifact
identity, trusted signatures, and proof receipts remain unresolved. This
Curve25519 boundary and the wider estate are not globally verified or signed;
verified-and-signed admission remains 0.

## Simplebox filesystem stdout authority checkpoint

The 42 unresolved calls in
`src/os/tools/simplebox/simplebox_fs_applets.spl` were all writes to the same
`stdout_write(text)` provider. They now route through one mandatory-inline
lexical `unsafe(ffi)` owner, leaving readlink, tee, cat, head, tail, and other
streaming filesystem applets safe at this boundary.

The rewrite preserves every message and output ordering. Mandatory inlining
prevents an added per-write frame; the 64 MiB file/input cap, 64 KiB chunks,
operand bounds, partial-write retry, and zero/invalid-progress rejection remain
unchanged. No filesystem read/write, allocation, copy, loop, branch, lookup,
lock, hash, signature operation, or runtime dispatch was added.

The focused authority/provider/performance ratchet passed. `stdout_write`
appears in only one typed registry, so provider closure remains incomplete.
Consolidating repeated boundary ownership changed the census as follows:

- raw call sites: 18,744 -> 18,703
- missing authority: 13,948 -> 13,906
- lexical unsafe: 3,406 -> 3,407
- function unsafe: unchanged at 1,390

Stdout error semantics, provider closure, exact artifact identity, trusted
signatures, and proof receipts remain unresolved. These applets and the wider
estate are not globally verified or signed; verified-and-signed admission
remains 0.

## GUI renderer staging-extent and authority checkpoint

`src/lib/nogc_sync_mut/ui/gui_renderer.spl` now declares its dynamic integer
call and borrowed string-pointer ABI explicitly unsafe alongside the existing
raw staging stores. Nine create, event, presentation, staging, and close owners
carry `ffi, raw_ptr` because they retain or invoke raw provider/object/function
handles.

Review found that full-frame presenters requested a `w*h` foreign staging
buffer but did not prove `pixels.len() == w*h`, allowing an oversized array to
write past it. A mandatory-inline helper now performs an overflow-safe exact
extent check using division/remainder before staging. The blit path also
validates positive destination dimensions and exact source extent before
requesting staging memory.

The new validation is O(1) once per present/blit, not inside the pixel loop.
Packed two-pixel `i64` stores, the odd final `i32` store, event decoding, cached
function addresses, and semantic pressed/presentation booleans remain
unchanged. No allocation, copy, per-pixel branch, symbol lookup, lock, hash,
signature operation, or dispatch layer was added.

The focused authority/provider/performance ratchet passed. Four of five used
symbols appear in both typed registries; `spl_str_ptr` appears in one. The
census changed as follows (a containing unsafe close owner supersedes its
nested lexical classification):

- raw call sites: unchanged at 18,671
- missing authority: 13,864 -> 13,829
- lexical unsafe: 3,412 -> 3,411
- function unsafe: 1,395 -> 1,431

String borrow lifetime, event/window ownership, exact dylib/ABI identity,
complete provider closure, trusted signatures, and proof receipts remain
unresolved. This renderer and the wider estate are not globally verified or
signed; verified-and-signed admission remains 0.

## Cross-platform event-handle authority checkpoint

`src/lib/nogc_async_mut/io/platform_event.spl` now declares all twenty epoll,
kqueue, IOCP, and event-port ABI families with explicit `ffi, raw_ptr`
authority. The seven create/register/deregister/poll/close owners carry the
same authority because they accept or return copyable native loop, descriptor,
and token integers and unverified flat event arrays.

Positivity checks are not ownership, backend branding, or exactly-once close.
IOCP completion semantics and event-port one-shot reassociation also cannot be
proved equivalent to the readiness facade from this wrapper alone. Therefore
these operations remain unsafe while backend detection, enum conversion, and
name queries stay safe.

The focused authority/provider/performance ratchet passed. Semantic register,
deregister, and close statuses remain `bool`; maximum-event validation and the
single O(1) enum dispatch remain unchanged. No poll, allocation, array copy,
loop, branch, lookup, lock, hash, signature operation, wrapper layer, or forced
inlining was added. Only one of twenty symbols appears in both typed
registries, eleven appear in one, and eight in neither. The census changed:

- raw call sites: unchanged at 18,671
- missing authority: 13,829 -> 13,801
- lexical unsafe: unchanged at 3,411
- function unsafe: 1,431 -> 1,459

Typed backend-branded ownership, exactly-once close, poll-array validation,
cross-backend semantic equivalence, provider closure, exact artifact identity,
trusted signatures, and proof receipts remain unresolved. This event facade
and the wider estate are not globally verified or signed; verified-and-signed
admission remains 0.

## QEMU runner environment/file/process authority checkpoint

`src/os/qemu_runner_part2.spl` now declares all seven local process, file,
environment, and time ABI families with explicit authority. Repeated
environment and file operations route through five mandatory-inline lexical
owners. Five functions that directly consume the process runner's aggregate
tuple and eight transitive build/cache/selection/run helpers carry `ffi`
authority.

The process call was deliberately not wrapped: an extra tuple-returning helper
would risk the native aggregate-return defect recorded elsewhere in the repo.
Every process launch remains at its original site with its original timeout,
arguments, output/error handling, and cache logic. Inline env/file owners add
no frame after optimization and no process, filesystem operation, allocation,
copy, scan, loop, branch, lookup, lock, hash, signature operation, or polling.

The focused authority/provider/performance ratchet passed. Six declarations
appear in both typed registries and file deletion appears in one. Consolidating
the 42 formerly unbounded calls changed the census as follows:

- raw call sites: 18,703 -> 18,671
- missing authority: 13,906 -> 13,864
- lexical unsafe: 3,407 -> 3,412
- function unsafe: 1,390 -> 1,395

Process aggregate ABI proof, environment transaction isolation, file-read
error semantics, complete provider closure, exact artifact identity, trusted
signatures, and proof receipts remain unresolved. This runner and the wider
estate are not globally verified or signed; verified-and-signed admission
remains 0.

## Driver source-parsing authority checkpoint

The phase-2 parsing driver now confines its seven raw process, environment,
stdout, and transient-array-scope ABIs to mandatory-inline lexical
`unsafe(ffi)` owners.  Environment lookup is truthfully nullable and
`rt_env_set` now preserves its provider boolean instead of declaring the
operation void.  Frontend-cache scope publication returns that status; its two
callers explicitly retain the result, while a failed publication safely leaves
the frontend cache disabled rather than fabricating cache admission.

All transient-scope success-path statuses remain checked.  Cleanup calls on an
already failing parse still preserve the primary error, and no successful
parse can ignore begin, pause, promotion, or end failure.  Mandatory inlining
keeps the existing call topology: no parser/source loop gains a foreign call,
allocation, copy, lookup, hash, lock, branch, or scan.

The focused static authority/performance ratchet passed.  The authoritative
census changed:

- raw call sites: 19,019 -> 18,996
- missing authority: 14,778 -> 14,748
- lexical unsafe: 3,284 -> 3,291
- function unsafe: unchanged at 957

Six symbols have typed-native plus interpreter registration.  `rt_stdout_flush`
is interpreter-registered but still absent from the typed-native registry, so
the audit deliberately records the lane gap rather than promoting the module.
No production self-hosted optimizer or benchmark was available.  Exact
artifact identity, signatures, and evidence admission remain absent;
verified-and-signed admission remains 0.

## Netstack IPC extent and authority checkpoint

The kernel IPC netstack dispatcher now rejects short socket, bind, listen,
connect, accept, send, receive, and close payloads before any payload read.
This closes the prior unsigned `payload_len - 4` underflow in the send path,
which could otherwise drive a very large byte-copy loop. Socket protocol
discriminants outside the declared TCP/UDP domain now return an IPC error
instead of being fabricated as UDP.

The 14 local MMIO declarations and the 10 raw IPC call owners carry explicit
`ffi`/`raw_ptr` authority. The unused file-local `unsafe_addr_of` declaration
was removed. The focused `netstack-ipc-sffi-authority.shs` ratchet covers 20
direct syscall/MMIO calls and confirms that none of the four MMIO primitives
is present in either hosted typed registry. Provider absence remains visible;
it is not treated as verification.

The authoritative census changed exactly by the 33 newly bounded calls:

- raw call sites: unchanged at 18,671
- distinct called symbols: unchanged at 3,260
- caller files: unchanged at 3,088
- missing authority: 13,801 -> 13,768
- lexical unsafe: unchanged at 3,411
- function unsafe: 1,459 -> 1,492

The dispatch adds one constant-time length comparison per request and no
allocation, copy, lookup, lock, hash, signature operation, or generic
dispatch. Valid send payloads retain the existing single linear copy loop.
The raw message-header allocation extent, kernel pointer lifetime, provider
artifact identity, and signed evidence admission remain unresolved. This
module and the wider SFFI estate are therefore not globally verified or
signed; verified-and-signed admission remains 0.

## Font provider authority checkpoint

`src/lib/nogc_sync_mut/sffi/spl_fonts.spl` now declares all eight raw dynamic
loader, function-address, byte-span, initializer, and layout ABI families with
explicit `ffi, raw_ptr` authority. Seventeen narrowly selected methods retain,
invoke, or transitively validate against those raw handles and therefore carry
the same caller-visible authority; provider-independent parsing remains safe.

The existing contract behavior is preserved: glyph presence remains `bool`,
foreign glyph pixels are validated then copied before the handle is freed, and
invalid provider state remains distinct from a valid empty glyph. No numeric
boolean workaround was introduced. No function was forced inline: the large
raster and layout loops keep their existing code-size and dispatch decisions,
and the annotation-only change adds no scan, hash, signature operation, lookup,
lock, allocation, copy, branch, or per-call work.

The focused static authority/provider/performance ratchet passed. Seven of the
eight symbols appear in both typed-native and interpreter registries; the
layout helper appears in only one. The census changed exactly by the 24
previously unbounded calls:

- raw call sites: unchanged at 18,846
- missing authority: 14,324 -> 14,300
- lexical unsafe: 3,402 -> 3,401 (the containing unsafe owner supersedes one
  nested lexical classification)
- function unsafe: 1,120 -> 1,145

This is authority accounting, not verification. Generic function-address ABI,
provider-global layout lifetime, typed resource ownership, exact artifact
identity, trusted signature admission, and proof receipts remain unresolved;
verified-and-signed admission remains 0.

## Host/GPU event-queue authority checkpoint

`src/lib/nogc_async_mut/gpu/engine2d/host_gpu_event_queue.spl` now declares all
fourteen process-global queue ABI families with explicit `ffi, raw_ptr`
authority. Eight narrowly selected direct and transitive owners cover reset,
emit, payload submit, submit/complete phases, and drain. Pure-Simple queue
state transitions and dispatch validation remain safe and unchanged.

This is a hot event lane, so the change is annotation-only. It preserves the
existing O(1) queue calls, payload copy behavior, data layout, semantic
`submitted`/`dispatched` booleans, and debug accounting. It introduces no new
loop, branch, allocation, copy, lookup, lock, hash, signature operation, or
dispatch layer, and deliberately adds no forced-inlining annotation.

The focused static authority/provider/performance ratchet passed. Five symbols
appear in both typed-native and interpreter registries, eight in one, and the
payload-text emitter in neither. The census changed exactly by the 43 formerly
unbounded calls:

- raw call sites: unchanged at 18,846
- missing authority: 14,300 -> 14,257
- lexical unsafe: unchanged at 3,401
- function unsafe: 1,145 -> 1,188

Provider-global synchronization, queue/backend handle branding, payload
lifetime, the missing provider, exact artifact identity, trusted signatures,
and proof receipts remain unresolved. This lane and the wider estate are not
globally verified or signed; verified-and-signed admission remains 0.

## Metal GPU-lane session authority checkpoint

`src/lib/gc_async_mut/gpu_lane/metal_lane_session.spl` now declares all 25
Metal ABI families with explicit authority. The availability and global-error
queries require `ffi`; every copyable device, queue, buffer, shader, pipeline,
command-buffer, and encoder handle additionally requires `raw_ptr`. Six
lifecycle/I/O methods—probe, initialization, arena upload/download, dispatch,
and shutdown—carry the minimal corresponding caller authority.

The implementation remains behaviorally unchanged. Existing bounds precede
arena allocation and transfer, status values remain semantic booleans where
declared, cleanup ordering is retained, and failed completion remains
quarantined rather than reported as success. The annotation-only change adds
no loop, branch, allocation, copy, lookup, lock, hash, signature operation, or
dispatch layer and deliberately adds no forced-inlining annotation.

The focused ratchet initially rejected a documentation-sensitive token count;
the audit itself was corrected to strip comments and declarations before
counting the 42 executable call sites, then passed. Twenty symbols appear in
both typed-native and interpreter registries, five in only one, and none in
neither. The global census changed exactly by those 42 calls:

- raw call sites: unchanged at 18,846
- missing authority: 14,257 -> 14,215
- lexical unsafe: unchanged at 3,401
- function unsafe: 1,188 -> 1,230

Metal object ownership, backend/device branding, exactly-once destruction,
mutable-download aliasing, cross-lane closure for five symbols, exact artifact
identity, trusted signatures, and proof receipts remain unresolved. This lane
and the wider estate are not globally verified or signed;
verified-and-signed admission remains 0.

## x86 filesystem-exec ring-3 loader authority checkpoint

`src/os/kernel/loader/x86_64_fs_exec_ring3.spl` now declares all eight local
serial, page-allocation, streaming, text-copy, heap-handoff, and exit-state ABI
families with explicit authority. Ten raw-memory and control-transfer owners
require `ffi, raw_ptr`; the owned text-to-byte length conversion uses one
minimal lexical `unsafe(ffi)` scope instead of making its caller unsafe.

The loader's executable admission remains unchanged: ELF and program-header
bounds, segment-count/image-span caps, overflow checks, user-range separation,
overlap rejection, W+X rejection including shared pages, and a file-backed
executable entry point are retained before mapping or transfer. The
annotation-only change adds no allocation, mapping, copy, loop, branch,
lookup, lock, hash, signature operation, dispatch layer, or forced inlining.

The focused authority/provider/performance ratchet passed. None of the eight
freestanding symbols appears in both typed registries, two appear in one, and
six appear in neither. That incomplete registry coverage remains explicit
rather than being treated as verification. The census changed exactly by the
39 formerly unbounded calls:

- raw call sites: unchanged at 18,846
- missing authority: 14,215 -> 14,176
- lexical unsafe: 3,401 -> 3,402
- function unsafe: 1,230 -> 1,268

Physical-page provenance, streaming destination extent, scheduler handoff,
freestanding provider closure, exact artifact identity, trusted signatures,
and proof receipts remain unresolved. This loader and the wider estate are not
globally verified or signed; verified-and-signed admission remains 0.

## Engine2D WM frame logging authority checkpoint

The production frame executor's 37 foreign calls were all writes to the same
scalar `serial_println(text)` provider. They now route through one
mandatory-inline `_engine2d_wm_log` owner containing the sole lexical
`unsafe(ffi)` call. This minimizes unsafe scope without marking negotiation,
damage planning, rendering, or receipt-validation methods unsafe.

The rewrite is mechanical and preserves every message and branch. Mandatory
inlining prevents an added per-frame call layer; no allocation, copy, scan,
loop, lookup, lock, hash, signature operation, or new dispatch was introduced.
The existing device receipt validation and checked MMIO presentation remain
unchanged.

The focused authority/provider/performance ratchet passed. `serial_println`
appears in only one typed registry, so provider closure remains incomplete.
Consolidating repeated boundary ownership changed the census as follows:

- raw call sites: 18,846 -> 18,810
- missing authority: 14,176 -> 14,139
- lexical unsafe: 3,402 -> 3,403
- function unsafe: unchanged at 1,268

Serial ordering/error semantics, cross-lane provider closure, exact artifact
identity, trusted signatures, and proof receipts remain unresolved. This frame
executor and the wider estate are not globally verified or signed;
verified-and-signed admission remains 0.

## SimpleOS GPU tensor authority checkpoint

`src/os/ml/gpu_tensor.spl` now declares all ten CUDA and scalar/array bridge
ABI families with explicit authority. Six `GpuTensor` methods and thirteen
top-level tensor operations that allocate, copy, duplicate, launch, mutate, or
free raw device authority require `ffi, raw_ptr`; the pure `ceil_div` helper
remains safe.

This checkpoint intentionally does not label the API safe. `GpuTensor` remains
a copyable integer device pointer, `reshape` aliases ownership, shape products
can overflow, allocation/transfer/launch status is not consistently checked,
and the reduction comment admits inputs larger than its single-block kernel can
handle. Fabricating a zero tensor or converting boolean status to integers
would hide those defects, so the existing behavior is retained and exposed as
unsafe pending a typed `Result`/resource redesign.

The focused authority/provider/performance ratchet passed. Of ten declarations
(nine currently called), two appear in both typed registries, one in only one,
and seven in neither. Semantic transfer/launch results remain `bool`. The
annotation-only change adds no branch, allocation, copy, synchronization,
kernel launch, lookup, hash, signature operation, wrapper dispatch, or forced
inlining. The census changed exactly by the 37 formerly unbounded calls:

- raw call sites: unchanged at 18,810
- missing authority: 14,139 -> 14,102
- lexical unsafe: unchanged at 3,403
- function unsafe: 1,268 -> 1,305

Typed ownership, overflow-safe shape validation, total status propagation,
reduction bounds, provider closure, exact artifact identity, trusted
signatures, and proof receipts remain unresolved. This tensor API and the
wider estate are not globally verified or signed; verified-and-signed
admission remains 0.

## AES-256-GCM foreign fast-path authority checkpoint

`src/os/crypto/aes256_gcm.spl` incorrectly described itself as having no SFFI
while calling two undeclared `rt_tls13_aes256_gcm_*` fast paths. Those
declarations are now explicit alongside `rt_bytes_u8_at`, and all three carry
`ffi` authority. The direct byte-lane loaders and public encrypt/decrypt fast
path owners are explicitly unsafe.

This is not a claim that the API is safe. The foreign fast paths encode
unsupported input, invalid input, and provider failure as an empty array that
falls through to Pure Simple. The byte accessor also relies on caller-proven
bounds, while public key/nonce/tag extent validation is incomplete. These
contracts require typed `Result`/status APIs before safe lifting.

No crypto data path changed. The focused ratchet preserves the constant-time
tag-difference accumulator, once-per-message AES-256 key expansion in GCTR,
semantic array results, and existing fallback. It adds no round, branch,
allocation, copy, lookup, lock, hash pass, signature operation, dispatch layer,
or forced inlining. The first ratchet run correctly exposed a tooling error
that counted three docstring references; the audit was fixed to strip
docstrings/comments/declarations before its passing executable-call count.

All three symbols appear in both typed registries. Making the two implicit
foreign calls explicit increased the authoritative raw-site inventory while
covering all 35 calls in this file:

- raw call sites: 18,810 -> 18,812
- missing authority: 14,102 -> 14,069
- lexical unsafe: unchanged at 3,403
- function unsafe: 1,305 -> 1,340

Input extents, unambiguous status, exact artifact identity, trusted signatures,
constant-time proof receipts, and provider semantic verification remain
unresolved. This cryptographic boundary and the wider estate are not globally
verified or signed; verified-and-signed admission remains 0.

## AudioManager resource-authority checkpoint

`src/lib/nogc_sync_mut/engine/audio/audio_manager.spl` now exposes foreign
resource authority through 24 narrowly selected direct and transitive owners.
Creation, clip loading/caching, playback, spatial mutation, listener mutation,
stop/pause/resume, volume propagation, unload, and shutdown carry `ffi` and,
where copyable handles participate, `raw_ptr`. Pure bus metadata getters and
updates remain safe.

The facade is not safely owned: engine, clip, and playback identities are
copyable integers; positivity is not backend branding or exactly-once
ownership. The raw spatialization ABI accepts numeric 0/1 and returns no
status. Changing only this caller to a boolean would neither change that ABI
nor repair its missing result contract, so the numeric raw call remains
explicitly unsafe while public stop/pause/resume results remain semantic
`bool`.

The focused authority/provider/performance ratchet passed. None of the 18 raw
symbols appears in either typed registry. The annotation-only change adds no
audio-buffer allocation/copy, dictionary operation, loop, branch, callback,
lookup, lock, dispatch, hash, signature operation, or forced inlining. The
census changed exactly by the 34 formerly unbounded calls:

- raw call sites: unchanged at 18,812
- missing authority: 14,069 -> 14,035
- lexical unsafe: unchanged at 3,403
- function unsafe: 1,340 -> 1,374

Typed resource ownership, backend branding, exactly-once teardown, raw
spatialization status, provider closure, exact artifact identity, trusted
signatures, and proof receipts remain unresolved. AudioManager and the wider
estate are not globally verified or signed; verified-and-signed admission
remains 0.

## OCB3 capacity and byte-access authority checkpoint

`src/os/crypto/ocb3.spl` described itself as having no SFFI despite using a
foreign byte accessor and 30 foreign capacity-reserving allocations. All
allocation sites now route through one mandatory-inline lexical `unsafe(ffi)`
owner. The byte accessor itself remains explicitly unsafe because its index
extent is caller-proven.

Replacing the allocator with empty arrays would remove one foreign dependency
but discard capacity hints, adding repeated growth allocations and copies for
large ciphertext/plaintext buffers. This checkpoint preserves every requested
capacity and therefore the existing allocation/memory behavior. It also
preserves the constant-time tag-difference accumulator and adds no branch,
loop, crypto operation, lookup, lock, hash pass, signature operation, or
runtime call after inlining. It does not return fabricated zero for an invalid
byte index.

The focused authority/provider/performance ratchet passed. The byte accessor
appears in both typed registries; the capacity allocator appears in only one.
Consolidating repeated boundary ownership changed the census as follows:

- raw call sites: 18,812 -> 18,783
- missing authority: 14,035 -> 14,004
- lexical unsafe: 3,403 -> 3,404
- function unsafe: 1,374 -> 1,375

Input/block extent proofs, capacity-provider closure, exact artifact identity,
trusted signatures, constant-time proof receipts, and semantic verification
remain unresolved. OCB3 and the wider estate are not globally verified or
signed; verified-and-signed admission remains 0.

## TLS 1.3 HKDF authority and UTF-8 extent checkpoint

`src/os/tls13/hkdf.spl` now declares all sixteen local text, byte, serial, and
specialized HKDF ABI families with explicit authority. Four foreign-fast-path
owners remain unsafe because their status/out or returned-array conventions
are not semantically verified. Owned text conversion and bounded byte reads use
two lexical `unsafe(ffi)` owners; the hot byte owner is mandatory-inline.

Review also found a correctness defect for unknown/non-ASCII labels: the code
encoded the label to UTF-8 bytes but bounded later indexing with `text.len()`.
Both SHA-256 and SHA-384 label encoders now use the actual already-produced
byte-array length, and the obsolete character-count helper was removed. This
is O(1) and introduces no encoding, scan, allocation, copy, branch, or loop.

The focused authority/provider/performance ratchet passed. Fourteen repeated
byte-access sites now route through one inline boundary, reducing duplicated
raw dispatch without changing the HKDF/HMAC loops. Of sixteen declarations,
one appears in both typed registries, eight in one, and seven in neither. The
census changed as follows:

- raw call sites: 18,783 -> 18,770
- missing authority: 14,004 -> 13,975
- lexical unsafe: 3,404 -> 3,406
- function unsafe: 1,375 -> 1,389

HKDF length limits, unambiguous status/result contracts, specialized-provider
closure, exact artifact identity, trusted signatures, and cryptographic proof
receipts remain unresolved. This TLS boundary and the wider estate are not
globally verified or signed; verified-and-signed admission remains 0.

## MIR switch/operator lowering authority checkpoint

MIR switch, operator, and call lowering now confines its two used raw ABI
families—nullable environment lookup and tagged-value discriminant—to
mandatory-inline lexical `unsafe(ffi)` owners.  The unused raw string-data and
string-length declarations were removed rather than granted authority.  Both
used symbols have typed-native and interpreter registration.

The sixteen source discriminant probes remain one-for-one at their existing
call/operator lowering sites.  Environment probes remain at their existing
debug/profile gates.  No second classification pass, allocation, copy, lookup,
hash, lock, branch, loop, or generic dispatch was added.

The focused static authority/performance ratchet passed.  The authoritative
census changed:

- raw call sites: 18,875 -> 18,857
- missing authority: 14,577 -> 14,557
- lexical unsafe: 3,320 -> 3,322
- function unsafe: unchanged at 978

Registration does not prove tagged-value layout, artifact identity,
signatures, or provenance.  No production self-hosted optimizer or benchmark
was available.  MIR expression lowering and the wider SFFI estate remain
neither globally verified nor signed; verified-and-signed admission remains 0.

## HIR item-lowering helper authority checkpoint

HIR item-lowering helpers now confine nullable environment lookup, process
termination, and transient graph promotion to three mandatory-inline lexical
`unsafe(ffi)` owners.  All three symbols have typed-native and interpreter
registration.

The bootstrap HIR publication path retains exactly fourteen graph-promotion
calls and combines every status into the existing total verdict.  Two fatal
paths previously continued if a defective `rt_exit` provider returned—one
could resume partial publication and the other indexed out of bounds.  Both
now panic after a returning exit provider.  This changes only a violated
noreturn contract and adds no work to valid execution.

The focused static authority/performance ratchet passed.  No graph walk,
allocation, copy, lookup, hash, lock, loop, or foreign call was added.  The
authoritative census changed:

- raw call sites: 18,893 -> 18,875
- missing authority: 14,619 -> 14,598
- lexical unsafe: 3,317 -> 3,320
- function unsafe: unchanged at 957

Registration does not prove promotion semantics, noreturn behavior, exact
artifact identity, signatures, or provenance.  No production self-hosted
optimizer or benchmark was available.  HIR helpers and the wider SFFI estate
remain neither globally verified nor signed; verified-and-signed admission
remains 0.

## AST declaration-node environment authority checkpoint

The flat declaration arena now confines its four environment ABIs to
mandatory-inline lexical `unsafe(ffi)` owners.  Text lookup is truthfully
nullable.  Integer lookup preserves its explicit default, and set/remove keep
semantic booleans rather than numeric substitutes.

The legacy bootstrap environment mirror previously ignored mutation failure,
which could retain a larger prior file's declaration tail and miscompile the
next file.  Mirror writes and removals now fail loudly.  Native/compiler normal
operation remains arena-preferred (`ast_decl_mode_cached = 1`) and therefore
does not execute those environment mutations.  On the compatibility path, the
new branch consumes the status of an already-existing libc operation; it adds
no environment scan, allocation, copy, lookup, hash, lock, loop, or foreign
call.

All four symbols have typed-native and interpreter registration.  The focused
static authority/performance ratchet passed.  The authoritative census changed:

- raw call sites: 18,912 -> 18,893
- missing authority: 14,642 -> 14,619
- lexical unsafe: 3,313 -> 3,317
- function unsafe: unchanged at 957

Registration does not prove process-environment isolation, exact artifact
identity, signatures, or provenance.  No production self-hosted optimizer or
benchmark was available.  The declaration arena and wider SFFI estate are not
globally verified or signed; verified-and-signed admission remains 0.

## Driver HIR-lowering authority checkpoint

The phase-3 HIR driver now confines all twelve raw ABI families.  Eleven use
mandatory-inline lexical `unsafe(ffi)` owners.  The existing
`driver_heap_ref_wellformed` owner deliberately remains a plain non-inlined
scalar-return function: inlining it can recreate the documented native
tuple-return-across-unsafe miscompile that caused malformed owners to be read
as success.  The focused ratchet pins this exception.

Environment lookup is truthfully nullable.  Source hashing, transient scope
begin/pause/promotion, promotion counters, process exit, and stdout flush keep
their existing invocation points.  No per-module hash, counter read, promotion,
allocation, copy, lookup, lock, branch, loop, or foreign call was added.

Provider coverage is explicitly incomplete:

- typed native and interpreter: 6 symbols
- typed native only: 4 promotion-counter symbols
- interpreter only: heap-reference formation and stdout flush

The authoritative census changed:

- raw call sites: 18,924 -> 18,912
- missing authority: 14,665 -> 14,642
- lexical unsafe: 3,302 -> 3,313
- function unsafe: unchanged at 957

No production self-hosted optimizer or benchmark was available.  Lane parity,
exact artifact identity, signatures, and evidence admission remain absent, so
HIR lowering and the wider SFFI estate are not globally verified or signed;
verified-and-signed admission remains 0.

## SMF mmap loader authority checkpoint

The native SMF mmap loader now declares all sixteen used runtime ABI families
as unsafe and confines every raw call to a lexical `unsafe(ffi)` owner. Twelve
reused operations have mandatory-inline owners; the four existing one-site
memory-lock and bulk-array operations retain their direct lexical blocks. The
unused page-size declaration was removed instead of receiving authority.

Twenty-one APIs that consume raw mapped addresses, relocation targets, or arbitrary
function pointers remain explicitly unsafe. Null/negative checks are retained,
but they are not mislabeled as proof of mapped extent, lifetime, relocation
bounds, or function signature. Status-returning operations keep their boolean
facades; pointer/sentinel ABIs keep their established numeric representation.

The hot-path shape is unchanged: mandatory inlining preserves direct runtime
calls, the packed-array executable-memory write still uses its single bulk
copy, and the boxed interpreter fallback remains the only byte loop. No lookup,
hash, signature check, lock, allocation, copy, generic dispatch, or second pass
was added. Static provider inventory across the typed-native and interpreter
registries found seven symbols in both registries, three in one registry, and
six in neither; registration remains an implementation gap, not proof.

The focused static authority/performance ratchet passed. The authoritative
census changed:

- raw call sites: 18,857 -> 18,850
- missing authority: 14,557 -> 14,538
- lexical unsafe: 3,322 -> 3,334
- function unsafe: unchanged at 978 (the census counts `ffi` authority; these
  twenty-one caller obligations are deliberately `raw_ptr` authority)

No production self-hosted build, optimizer, benchmark, proof receipt, artifact
signature, or loader admission was run. The SMF mmap loader and wider SFFI
estate remain neither globally verified nor signed; verified-and-signed
admission remains 0.

Follow-up caller review removed the loader copy's remaining fabricated-zero
function-call contract. All four arbitrary-address helpers now reject null or
negative addresses as `Result.Err` and return successful foreign values as
`Result.Ok`; the loaded-main dispatcher propagates that result directly inside
minimal `raw_ptr` authority instead of wrapping it in a second `Ok`. This adds
no success-path allocation, lookup, or dispatch beyond the pre-existing
`Result` contract already used by the parallel top-level implementation.

## Shared executable mapper caller-authority checkpoint

The shared loader/JIT executable mapper now enters `raw_ptr` authority only at
the twelve calls that consume mapping records it created and owns. The safe
mapper surface still performs the same linear allocation, one bulk code write,
RW-to-RX transition, instruction-cache flush, and address lift; no additional
pass, lookup, allocation, copy, lock, or dispatch was introduced.

Relocation validation now checks the complete four- or eight-byte write extent
before deriving the patch address, and rejects signed address-addition overflow.
The previous first-byte-only check could admit an eight-byte write beginning in
the last seven bytes of a mapping. The five existing relocation writes remain
one-for-one inside minimal authority blocks.

The focused static authority/bounds/performance ratchet passed. This caller
propagation does not change the raw-call census because it governs typed Simple
facades rather than new runtime ABI calls. No production compiler, optimizer,
runtime memory-safety tool, or benchmark was available, so executable mapping
remains unverified beyond the static ratchet and is not signed.

Adjacent module-loader propagation now confines its two owned mapping
protection transitions and two validated entry-point calls to four minimal
`raw_ptr` blocks. Two unused raw-memory imports were removed. Relocation,
cache, and symbol-table algorithms are unchanged, and no authority was widened
to the loader function or module level.

## Compatibility loader caller-authority checkpoint

The compatibility loader now confines its eleven executable-memory operations
to minimal `raw_ptr` blocks while preserving its existing single-pass load and
relocation flow. Relocation bounds cover the complete four/eight-byte write and
reject address-addition overflow before entering authority. The two native-main
calls continue propagating typed `Result` values.

Review also found that failures after one or more executable allocations can
leak candidate mappings and provisional global-symbol entries. That broader
transactional defect is recorded at
`doc/08_tracking/bug/compat_loader_partial_exec_mapping_rollback_2026-08-25.md`
with fail-path and performance acceptance criteria. It was not hidden by a
local cleanup that would leave earlier mappings leaked. The focused static
authority/bounds/single-pass ratchet passed; production RSS and allocation
evidence remain unavailable.

## mmap provider-contract and registration checkpoint

All nine raw mmap/file-descriptor ABI families now have typed native signature
entries and interpreter registrations. The six previously missing interpreter
providers (`madvise`, `msync`, `mlock`, `munlock`, descriptor open, and close)
now call the corresponding Unix APIs with exact arity and fail closed on
unsupported hosts. Descriptor paths reject interior NUL rather than truncating.

The C providers now reject null addresses, nonpositive lengths, negative mmap
offsets, null paths, and negative descriptors before signed values can wrap to
large platform sizes. Windows `madvise`, which has no implementation, now
returns failure instead of fabricated success. The loader-copy allocator was
also changed from RWX to RW, retaining its existing explicit RX transition.

These checks add one predictable boundary branch and no lookup, lock, heap
allocation, copy, or generic dispatch to memory syscalls. Interpreter path-to-C
conversion retains the one required `CString` allocation per descriptor open;
no allocation was added to mapping/status hot paths. The focused provider,
null/length, W^X, and registration audit passed. `cargo check` for the Rust
compiler completed successfully in 46.26 seconds with four pre-existing
warnings outside the changed provider logic.

This establishes provider presence and compile correctness, not artifact
identity, proof, sanitizer coverage, or signatures. The nine providers remain
unsafe boundary code and verified-and-signed admission remains 0.

## Generic dynamic-dispatch typed-admission checkpoint

The legacy dynamic resolver may now publish a generic function pointer only
when the compiler-owned runtime registry declares an exact all-`i64` parameter
list and exactly one `i64` result matching the call arity. Unknown symbols,
mixed-width parameters/results, void returns, and arity mismatches fail with
typed SFFI conversion errors before `dlsym` publication or invocation. The
specialized scoped byte/font adapters remain independent typed owners.

Admission is deliberately cold-path. Each main-runtime, satellite, or manifest
symbol cache stores the admitted address and arity. The existing cache miss
does the registry scan once; cached calls retain the existing hash lookup and
add only one integer arity comparison. `call_fptr` performs no registry scan,
allocation, new lookup, or new lock. Its fixed stack argument array and arity
cap remain unchanged.

The focused static admission/performance ratchet passed. All 15 focused
dynamic-SFFI unit tests passed (0 failures); the optimized test build/link took
3m32s and the tests themselves completed in 0.00s. This closes name-only and
mixed-width admission for the legacy path, but an exact integer signature is
still not artifact identity, ownership proof, signature verification, or a
general typed thunk. Verified-and-signed admission remains 0.

## Runtime-value facade authority checkpoint

`src/lib/nogc_sync_mut/sffi/runtime.spl` now preserves authority instead of
turning raw runtime-value integer handles into apparently safe values. GC init
and collection are the only safe facades and use minimal lexical `unsafe(ffi)`;
the other 31 handle-producing/consuming facades explicitly retain `ffi` and
`raw_ptr` caller obligations. All 33 wrappers are mandatory-inline, so the
change adds no call frame, allocation, copy, branch, lookup, or dispatch.

Semantic predicates and comparisons remain `bool`; they were not converted to
numeric status workarounds. Provider inventory is incomplete: of 32 declared
symbols, six appear in both typed-native and interpreter registries, eight in
one registry, and eighteen in neither. Consequently this module is not safe or
verified merely because its authority is now honest.

The focused static authority/provider/performance ratchet passed. The current
census changed:

- raw call sites: unchanged at 18,846
- missing authority: 14,526 -> 14,493
- lexical unsafe: 3,342 -> 3,344
- function unsafe: 978 -> 1,009

No production optimizer/runtime test was run for this Pure Simple annotation
change. Missing providers, raw handle validity, ownership, artifact identity,
and signatures remain open; verified-and-signed admission remains 0.

## System facade authority checkpoint

`src/lib/nogc_sync_mut/sffi/system.spl` now confines all 41 raw calls without
blanket authority. Twenty-nine total scalar, optional, status, process, and
time operations use minimal lexical `unsafe(ffi)` owners. Thirteen public
facades whose types still conflate failure with empty runtime-owned text,
untyped discriminants, parser sentinels, or snapshot ownership remain
explicitly unsafe. Optional environment absence remains `text?`, and semantic
mutation/kill results remain `bool` rather than numeric workarounds.

All direct raw owners are mandatory-inline. This adds no call frame, allocation,
copy, lookup, lock, branch, or generic dispatch; existing PID validation and
process execution behavior are unchanged. Provider inventory remains
incomplete: of 39 declared symbols, twelve appear in both typed-native and
interpreter registries, six in one registry, and twenty-one in neither.

The focused static authority/provider/performance ratchet passed. The census
changed:

- raw call sites: unchanged at 18,846
- missing authority: 14,493 -> 14,460
- lexical unsafe: 3,344 -> 3,365
- function unsafe: 1,009 -> 1,021

No production optimizer/runtime test was run for this Pure Simple annotation
change. The thirteen ambiguous facades require typed `Option`/`Result` redesign,
and provider/artifact/signature evidence remains absent; verified-and-signed
admission remains 0.

## I/O facade authority checkpoint

`src/lib/nogc_sync_mut/sffi/io.spl` now confines every raw call while keeping
authority narrow. Eighteen direct filesystem scalar/status facades plus the
four existing nullable-read and lock owners use lexical `unsafe(ffi)`.
Fourteen runtime-owned text/array/path facades remain unsafe because their
types do not represent failure or ownership. Raw lock acquire/release and the
two deprecated descriptor APIs also remain explicitly unsafe; the resource
wrapper grants authority only while it owns a live descriptor.

Semantic filesystem results remain `bool`, and nullable line/mmap reads retain
their existing `Result` lift. All 36 direct raw owners are mandatory-inline, so
no extra call frame, filesystem probe, read, allocation, copy, lookup, branch,
or dispatch was introduced. Provider inventory found 25 of 34 symbols in both
typed-native and interpreter registries, three in one, and six in neither.

The focused static authority/provider/performance ratchet passed. The census
changed:

- raw call sites: unchanged at 18,846
- missing authority: 14,460 -> 14,428
- lexical unsafe: 3,365 -> 3,381
- function unsafe: 1,021 -> 1,037

No production optimizer/runtime test was run for this Pure Simple annotation
change. Ambiguous result types, missing providers, artifact identity, and
signatures remain open; verified-and-signed admission remains 0.

## AST facade authority checkpoint

`src/lib/nogc_sync_mut/sffi/ast.spl` now keeps 27 expression, argument, and
node handle operations explicitly unsafe. The facade uses raw `i64` handles
and does not validate tag, lifetime, ownership, or indexed-child bounds, so a
zero check or a safe-looking wrapper would not discharge the contract. Only
process-global registry count/clear remain safe behind two lexical owners.

Semantic literal projection remains typed (`bool`, `i64`, `f64`, optional
text); no numeric workaround was introduced. All 29 wrappers are
mandatory-inline, adding no call frame, traversal, allocation, copy, lookup,
branch, or dispatch. Provider inventory found every symbol in exactly one of
the typed-native/interpreter registries and none in both, so cross-lane closure
is wholly incomplete.

The focused static authority/provider/performance ratchet passed. The census
changed:

- raw call sites: unchanged at 18,846
- missing authority: 14,428 -> 14,399
- lexical unsafe: 3,381 -> 3,383
- function unsafe: 1,037 -> 1,064

No production optimizer/runtime test was run for this Pure Simple annotation
change. Typed resources, cross-lane providers, artifact identity, and signatures
remain absent; verified-and-signed admission remains 0.

## Audio facade authority checkpoint

`src/lib/nogc_sync_mut/io/audio_sffi.spl` now keeps 21 device, source,
playback, SDL-backend, spatial-source, and raw PCM buffer facades explicitly
unsafe. Its `AudioEngine`/`AudioSource`/`AudioPlayback` values are copyable
integer handles without exactly-once ownership or backend branding, so an
`is_valid` flag cannot make shutdown, close, or cross-backend use safe.

Fourteen global volume/count/backend/listener/capture operations join the
existing pitch adapter behind minimal lexical `unsafe(ffi)`. Semantic state and
status results remain `bool`; no numeric workaround was introduced. All 36
Simple wrappers that call raw audio operations are mandatory-inline, adding no
call frame, audio-buffer copy, allocation, lookup, lock, branch, or dispatch.

The focused static authority/provider/performance ratchet passed. None of the
39 declarations appears in either the typed-native registry or interpreter
dispatch, so the module currently has zero cross-lane registered providers.
The census changed:

- raw call sites: unchanged at 18,846
- missing authority: 14,399 -> 14,364
- lexical unsafe: 3,383 -> 3,397
- function unsafe: 1,064 -> 1,085

No production optimizer/audio runtime test was run for this Pure Simple
annotation change. Typed resources, backend-branded handles, registrations,
artifact identity, and signatures remain absent; verified-and-signed admission
remains 0.

## Vulkan facade authority checkpoint

`src/lib/nogc_sync_mut/io/vulkan_sffi.spl` now keeps 33 device-selection,
buffer, shader, pipeline, descriptor, command, image, sampler, framebuffer,
swapchain, and ambiguous-error facades explicitly unsafe. The wrapper structs
are copyable integer handles without ownership, device/backend branding, or
command-order state, so `is_valid` cannot make destruction or cross-object use
safe. The two helper-to-wrapper propagation points remain unsafe as well.

Only availability, global init/shutdown status, device count, and device idle
wait remain safe behind five lexical owners. Semantic statuses remain `bool`.
All 38 wrapper/helper paths are mandatory-inline, adding no command traversal,
allocation, buffer copy, lookup, lock, branch, or dispatch.

The focused static authority/provider/performance ratchet passed. Among the 39
used symbols (40 calls), 21 appear in both typed-native and interpreter
registries, ten in one, and eight in neither. The census changed:

- raw call sites: unchanged at 18,846
- missing authority: 14,364 -> 14,324
- lexical unsafe: 3,397 -> 3,402
- function unsafe: 1,085 -> 1,120

No production optimizer/Vulkan runtime test was run for this Pure Simple
annotation change. Typed resources, device/order validation, remaining
providers, artifact identity, and signatures remain absent;
verified-and-signed admission remains 0.

## Top-level SMF mmap compatibility authority checkpoint

The distinct top-level SMF mmap implementation now declares all twenty used
runtime ABI families unsafe and confines every raw call to lexical
`unsafe(ffi)`. Eight repeated file/mapping operations use mandatory-inline
owners; twelve existing one-site byte, relocation, locking, and function-call
operations retain direct lexical blocks. The unused page-size declaration was
removed.

Seventeen address-consuming APIs retain explicit `raw_ptr` caller authority.
The existing function-call facades continue returning `Result<i64, text>` for
invalid addresses rather than manufacturing zero. The implementation's stronger
W^X policy is pinned: allocation remains RW and the existing transition makes
pages RX; no RWX allocation was introduced.

The hot path remains one raw call per operation. Mandatory inlining adds no
dispatch, and the packed code-copy path remains a single bulk call with only
the existing interpreter fallback loop. No admission hash, signature check,
lookup, lock, allocation, copy, or extra traversal was added. Static registry
inventory found eleven symbols in both typed-native and interpreter registries,
three in one registry, and six in neither.

The focused static authority/W^X/performance ratchet passed. The authoritative
census changed:

- raw call sites: 18,850 -> 18,846
- missing authority: 14,538 -> 14,526
- lexical unsafe: 3,334 -> 3,342
- function unsafe: unchanged at 978 (`raw_ptr`-only caller obligations are not
  classified as `ffi` function authority by the census)

No production self-hosted build, optimizer, benchmark, proof receipt, artifact
signature, or loader admission was run. This compatibility loader and the wider
SFFI estate remain neither globally verified nor signed; verified-and-signed
admission remains 0.

## MIR function-lowering authority checkpoint

MIR function lowering now confines its tagged-value discriminant ABI and five
raw environment reads inherited through a glob import to two mandatory-inline
lexical `unsafe(ffi)` owners.  The return-type debug gate now decodes nullable
environment absence before comparison.  Both symbols have typed-native and
interpreter registration.

The discriminant primitive is used 26 times in type lowering and diagnostics.
The focused ratchet pins that count and mandatory inlining, so the change adds
no second classification, allocation, copy, lookup, hash, lock, branch, loop,
or generic dispatch.  Environment probes remain at their existing cached or
debug-gated sites.

The source census recognizes the locally declared discriminant family (the
glob-imported environment family remains outside its documented lower-bound
model).  It changed exactly as expected:

- raw call sites: 18,949 -> 18,924
- missing authority: 14,691 -> 14,665
- lexical unsafe: 3,301 -> 3,302
- function unsafe: unchanged at 957

Provider registration does not prove tagged-value layout, artifact identity,
signatures, or provenance.  No production self-hosted optimizer or benchmark
was available.  MIR lowering and the wider SFFI estate are not globally
verified or signed; verified-and-signed admission remains 0.

## Flat AST module-assembly authority checkpoint

Flat AST module assembly now confines its seven environment, timing, and
transient-lifetime ABIs to mandatory-inline lexical `unsafe(ffi)` owners.
Environment reads are truthfully nullable and mutation preserves the provider
boolean.  All seven symbols have typed-native and interpreter registration.

Review fixed ignored lifetime results that could previously publish a
`ParserModule` after failed transient scope begin, pause, graph promotion, or
end.  Those paths now fail loudly.  Cache-hit environment restoration failure
returns a miss (`nil`) so the caller reparses; the ordinary parse path rejects
failed restoration instead of continuing with contaminated lexer state.

The checks consume status values the foreign calls already returned.  Timing
calls remain behind the existing cached profile flag, and no AST/decl loop
gains a call, allocation, copy, lookup, hash, lock, branch, or scan.

The focused static authority/performance ratchet passed.  The authoritative
census changed:

- raw call sites: 18,996 -> 18,974
- missing authority: 14,748 -> 14,719
- lexical unsafe: 3,291 -> 3,298
- function unsafe: unchanged at 957

Registration and source checks do not prove transient-heap implementation,
artifact identity, signatures, or provenance.  No production self-hosted
optimizer or benchmark was available.  Flat AST assembly and the wider SFFI
estate remain neither globally verified nor signed; verified-and-signed
admission remains 0.

## Hosted runtime-compiler authority checkpoint

The hosted C-runtime compiler now confines filesystem existence/deletion,
absolute-path resolution, process execution, environment lookup, and PID
retrieval to six mandatory-inline lexical `unsafe(ffi)` owners.  Environment
and absolute-path results are truthfully optional and decoded before text use;
the former mixed text/`nil` comparisons and three broader unsafe blocks were
removed.

The C-source loop retains one required-source existence probe and at most one
compiler process execution per uncached source.  Cache checks, cache
publication, cleanup, object arrays, compiler arguments, and process output
copies are unchanged.  The ownership change adds no allocation, copy, lookup,
hash, lock, branch, loop, or foreign call.

The focused static authority/performance ratchet passed.  The authoritative
census changed:

- raw call sites: 18,974 -> 18,949
- missing authority: 14,719 -> 14,691
- lexical unsafe: 3,298 -> 3,301
- function unsafe: unchanged at 957

Five symbols have typed-native plus interpreter registration.  Temporary-file
deletion is interpreter-registered but absent from the typed-native registry;
cleanup is best-effort, but that provider gap blocks verified promotion.  No
production self-hosted optimizer or benchmark was available.  Exact artifact
identity, signatures, and evidence admission remain absent, so the runtime
compiler and wider SFFI estate are not globally verified or signed;
verified-and-signed admission remains 0.

## RISC-V boot-services authority checkpoint

`riscv_services.spl` had twelve PCI/network/storage/log interfaces and 63
ambient calls.  All declarations are explicitly tagged and all calls now use
mandatory-inline `ffi` owners.  The focused
`riscv-services-sffi-authority.shs` ratchet passed and keeps eleven target-owned
symbols tied to the repository's authoritative unbacked-extern baseline rather
than treating example-tree C implementations as production evidence.

Review found three fail-open classes.  An untrusted PCI device count could
drive an effectively unbounded boot scan; values outside 0..256 now reject the
scan.  Storage initialization/read/NVFS statuses now use the same wrapped-signed
decoder as network statuses, so encoded negative failures cannot become
success.  A successful TCP bind no longer declares the network ready when its
close probe fails.  These add constant-time boot-only checks.  No per-packet,
per-sector, steady-state loop, allocation, copy, lookup, lock, hash, signature
operation, or generic dispatch changed.

Readiness state remains semantic Simple `bool`; signed `i64` values are retained
only for foreign status/error carriers.  This fixes status interpretation
rather than replacing booleans with numbers.

The authoritative call census changed as follows:

- raw call sites: 19,262 -> 19,211
- lexical unsafe: 3,244 -> 3,256
- function unsafe: unchanged at 919
- missing authority: 15,099 -> 15,036

The file now reports twelve raw rows, all lexically authorized, and zero missing
authority.  Because eleven production providers are still unbacked and no
exact artifact is signed, this lane remains explicitly unsafe;
verified-and-signed admission remains 0.

## VHDL design-catalog authority checkpoint

The design-wide VHDL catalog now confines its four foreign ABI families to
mandatory-inline lexical `unsafe(ffi)` owners.  The environment read is
truthfully nullable; dictionary membership remains a semantic boolean, and
tagged-value discriminant/payload retain their signed runtime-word contracts.

Catalog construction contains nested scans and repeated dictionary probes, so
the performance ratchet pins the owners as direct-inline primitives.  The
change adds no lookup structure, allocation, copy, hash, lock, branch, loop,
or foreign call on the valid path and does not alter the catalog algorithms or
their asymptotic complexity.

The authoritative census changed exactly by routing 41 recognized direct
calls through four owners:

- raw call sites: 19,085 -> 19,048
- missing authority: 14,889 -> 14,848
- lexical unsafe: 3,277 -> 3,281
- function unsafe: unchanged at 919

All four symbols are present in both the typed native registry and interpreter
registration.  Provider registration still does not prove dictionary handle
validity, tagged-value layout, artifact identity, signatures, or provenance.
No production self-hosted optimizer or benchmark was available, so this
module and the wider SFFI estate are not globally verified or signed;
verified-and-signed admission remains 0.

## Minimal raw-runtime SFFI unsafe-surface checkpoint

`sffi_minimal.spl` intentionally exposes integer-encoded runtime pointers and
handles.  Because no wrapper can establish handle validity, ownership, or
provider identity, all 41 smallest wrapper functions are now explicitly
`unsafe(ffi)` rather than presenting a safe-looking API around a lexical raw
call.  This is the narrowest honest unsafe boundary: each wrapper contains
exactly one existing foreign call and no additional owner layer.

Two fabricated-value contracts were corrected.  Raw environment lookup and
deep array release now preserve `i64?` absence instead of collapsing `nil` to
zero, and invalid negative GC allocation size returns the ABI's documented
null-failure sentinel `0` rather than the pointer-like value `-1`.  Repository
search found no consumers of the changed optional wrappers.

Provider coverage confirms this module cannot be declared safe or verified:

- typed native registry and interpreter: 14 symbols
- typed native registry only: 3 symbols
- interpreter only: 6 symbols
- neither registry: 18 symbols

The focused unsafe-surface ratchet passed.  The authoritative census changed:

- raw call sites: unchanged at 19,048
- missing authority: 14,848 -> 14,810
- lexical unsafe: unchanged at 3,281
- function unsafe: 919 -> 957

This metadata-only ownership change adds no call, allocation, copy, lookup,
lock, hash, branch, or loop.  It deliberately does not add nominal inline
owners because each unsafe wrapper already directly invokes its raw ABI once.
No production self-hosted optimizer or benchmark was available.  Exact
artifact identity, ABI proof, signatures, and evidence admission remain
absent, so verified-and-signed admission remains 0.

## Interpreter module-resolution authority checkpoint

The module path resolver now confines environment lookup, path joining, and
dirname to three mandatory-inline lexical `unsafe(ffi)` owners.  `SIMPLE_LIB`
is declared nullable and decoded to the existing empty/unset configuration
before comparison or path construction, removing the former comparison of an
unvalidated optional result with both text and `nil`.

Resolution already caches module-only and caller-relative outcomes and keeps
underscore-transparent recursion on the miss path.  The change preserves those
algorithms and every existing filesystem probe.  Mandatory inlining adds no
path allocation, lookup, foreign dispatch, hash, lock, copy, branch, loop, or
tree scan to the hot resolution path.

The focused static ratchet passed and confirms all three symbols are registered
for typed native and interpreter lanes.  The authoritative census changed:

- raw call sites: 19,048 -> 19,019
- missing authority: 14,810 -> 14,778
- lexical unsafe: 3,281 -> 3,284
- function unsafe: unchanged at 957

Registration does not prove platform path semantics, filesystem race freedom,
artifact identity, signatures, or provenance.  No production self-hosted
optimizer or benchmark was available, so module resolution and the wider SFFI
estate are not globally verified or signed; verified-and-signed admission
remains 0.

## LLVM-library expression translation authority checkpoint

`llvm_lib_translate_expr.spl` had six local declarations; unused
`rt_text_eq_any` and `rt_ptr_read_i64` boundaries are removed.  The four active
array/enum/tuple interfaces now use mandatory-inline `ffi` owners, while the
existing environment-policy lookup remains in its minimal lexical scope.  The
focused `llvm-lib-translate-expr-sffi-authority.shs` ratchet passed, pins the
C/Rust array providers and compiler ABI registry, and preserves enum/tuple
probe counts.

Five `rt_array_push_i64_raw` results were previously discarded while building
LLVM GEP, call-argument, and parameter-type vectors.  Allocation/capacity
failure could therefore emit a shorter vector and continue compilation.  The
owner now traps on false status.  Each valid append gains one unlikely status
comparison with no new allocation, copy, lookup, lock, hash, signature
operation, or generic dispatch.  Translation algorithms and data layout remain
unchanged.

The authoritative call census changed as follows:

- raw call sites: 19,305 -> 19,262
- lexical unsafe: 3,240 -> 3,244
- function unsafe: unchanged at 919
- missing authority: 15,146 -> 15,099

The file now reports five raw rows, all lexically authorized, and zero missing
authority.  LLVM provider proofs and exact signed compiler artifacts remain
absent, so verified-and-signed admission remains 0.

## Compiler lexer authority checkpoint

The core lexer had four genuine file/environment/array runtime interfaces and
47 ambient calls.  All declarations are now explicitly tagged and all calls
route through mandatory-inline `ffi` owners.  The focused
`compiler-lexer-sffi-authority.shs` ratchet passed, pins the compiler ABI
registry, and proves the per-character embedded-NUL validation loop remains
free of foreign dispatch.

`rt_file_read_text` and `rt_env_get` incorrectly promised non-optional text
despite existing callers using `??` for read failure/unset state.  Their
declarations now truthfully return `text?`.  Environment writes remain
best-effort mirrors of authoritative module state, as required by the guest
lane where env get/set may be unavailable; ignoring their boolean status does
not manufacture lexer success.  No token loop, character scan, environment
operation count, allocation, copy, cache, lock, hash, signature operation, or
generic dispatch changed.

The authoritative call census changed as follows:

- raw call sites: 19,348 -> 19,305
- lexical unsafe: 3,236 -> 3,240
- function unsafe: unchanged at 919
- missing authority: 15,193 -> 15,146

The file now reports four raw rows, all lexically authorized, and zero missing
authority.  Provider proof and exact signed compiler artifacts remain absent,
so verified-and-signed admission remains 0.

## Parser type-expression authority checkpoint

`parser_types_expr.spl` had five genuine environment/diagnostic/enum/tuple
runtime interfaces and 51 ambient calls.  All are now explicitly tagged and
routed through mandatory-inline `ffi` owners.  The focused
`parser-types-expr-sffi-authority.shs` ratchet passed, pins the compiler ABI
registry entries, and preserves the exact number of parser discriminant,
payload, tuple, and diagnostic operations.

The `rt_env_get` declaration incorrectly promised non-optional `text` even
though the trace gate already handled absence with `?? ""`.  It now declares
`text?`, matching the provider and caller semantics without adding a branch or
lookup.  No parser loop, enum sample construction, allocation, copy, cache,
lock, hash, signature operation, or generic dispatch changed.  Discriminant
caching remains deferred until production profiles can prove it improves the
different compiler lanes without extending object lifetimes.

The authoritative call census changed as follows:

- raw call sites: 19,394 -> 19,348
- lexical unsafe: 3,231 -> 3,236
- function unsafe: unchanged at 919
- missing authority: 15,244 -> 15,193

The file now reports five raw rows, all lexically authorized, and zero missing
authority.  Provider proof and exact signed compiler artifacts remain absent,
so verified-and-signed admission remains 0.

## ARM filesystem-exec VFS authority checkpoint

The ARM filesystem-exec VFS declared eleven foreign interfaces; the unused
`rt_arm_virtio_blk_read_hello_smf` boundary is removed, and all 94 ambient
calls to the ten active array/VirtIO/log/trace interfaces are routed through
mandatory-inline `ffi` owners.  The focused
`arm-fs-exec-vfs-sffi-authority.shs` ratchet passed and pins the six entries
that exist in the compiler ABI registry.

Review corrected two fail-open behaviors.  A late device initialization no
longer continues into filesystem reads after its FAT32 BPB probe fails.  The
multi-sector cluster and file-chain loops no longer discard short-append
status; they stop with the bytes actually established instead of continuing as
if the requested extent was appended.  Valid append iterations gain one
status comparison.  Sector and boot-probe paths hoist stable length projections,
removing two redundant calls.  Allocation count, byte copies, I/O request
count, data layout, and asymptotic work are otherwise unchanged; failed paths
perform less work.

Provider admission remains incomplete.  `arm_fs_exec_trace`,
`rt_arm_array_append_bytes`, `rt_arm_fat32_probe_bpb_from_virtio`, and
`rt_arm_virtio_blk_read_prefix` remain in the repository's authoritative
unbacked-extern baseline.  Example-tree C implementations are migration
evidence, not proof that the loaded production artifact owns those symbols.
The `[u8]` read API also still conflates empty files and some read failures.

The authoritative call census changed as follows:

- raw call sites: 19,478 -> 19,394
- lexical unsafe: 3,221 -> 3,231
- function unsafe: unchanged at 919
- missing authority: 15,338 -> 15,244

The file now reports ten raw rows, all lexically authorized, and zero missing
authority.  It remains explicitly unsafe and unverified; verified-and-signed
admission remains 0.

## AOT native-output driver authority checkpoint

The native-output driver now gives each of its 13 foreign ABI families one
mandatory-inline owner and confines the raw call to a minimal lexical
`unsafe(ffi)` scope.  Filesystem and capability predicates retain semantic
`bool` results, process execution retains its signed `i64` exit status, and
file/environment reads now truthfully declare absence with `text?`.

Review also removed fail-open cache setup behavior.  Failure to create or
clean the cache scope, consume the one-build clean flag, or write the phase and
lane-ownership markers now returns `CompileResult.CodegenError`.  Existing
copy, object-write, archiver, relocatable-link, and receipt failures were
already checked and remain fail closed.

The focused static authority/performance ratchet passed.  The authoritative
census changed as expected:

- raw call sites: 19,152 -> 19,119
- missing authority: 14,976 -> 14,930
- lexical unsafe: 3,257 -> 3,270
- function unsafe: unchanged at 919

The reduction in recognized call sites comes from routing 46 former direct
calls through 13 owners.  `@always_inline` preserves one foreign dispatch per
operation; no hashing, lookup, lock, allocation, copy, or loop was added.  The
source-fingerprint loop still performs exactly one existing foreign hash per
source plus one final manifest hash.  No production self-hosted optimizer or
benchmark was available.

This checkpoint does not authenticate runtime/provider artifacts.  Native
provider coverage remains lane-dependent (notably stdout flush and SIMD query
are interpreter-registered rather than present in the typed native registry),
and the existing non-cryptographic `rt_hash_text` is cache identity rather than
security evidence.  The AOT boundary and the wider SFFI estate are therefore
not globally verified or signed; verified-and-signed admission remains 0.

## HIR module-surface authority checkpoint

`module_surface_registry.spl` had two genuine runtime interfaces and 63
ambient call sites: one content hash and 62 transient-heap ownership
promotions.  Both declarations are now explicitly tagged and every call is
routed through one of two mandatory-inline `ffi` owners.  The focused
`hir-module-surface-sffi-authority.shs` ratchet passed, pins the compiler-owned
ABI registry, and preserves the exact promotion count and order.

Every promotion result was already either checked by the existing
short-circuit/failure diagnostic path or returned as the function's final
boolean result; no fabricated success was found.  The change adds no graph
operation, environment access, allocation, copy, loop, lookup, lock, hash,
signature operation, or generic dispatch.  Its O(total retained surface
fields) ownership work and failure attribution are unchanged.

The authoritative call census changed as follows:

- raw call sites: 19,539 -> 19,478
- lexical unsafe: 3,219 -> 3,221
- function unsafe: unchanged at 919
- missing authority: 15,401 -> 15,338

The file itself now reports two raw rows, both lexically authorized, and zero
missing authority.  Runtime ownership proof and exact signed compiler artifacts
remain absent, so verified-and-signed admission remains 0.

## MIR expression-dispatch authority checkpoint

The largest remaining compiler file was a genuine boundary rather than census
noise.  `expr_dispatch.spl` declared five runtime functions directly; the
unused `rt_dict_contains` declaration is removed, and all calls to the four
active environment/enum/tuple interfaces are routed through mandatory-inline
`ffi` owners.  The focused `mir-expr-dispatch-sffi-authority.shs` ratchet
passed, pins the compiler-owned ABI registry, and preserves the exact number
of runtime probes in the lowering logic.

This file is on MIR lowering's hot path.  The change adds no runtime enum
probe, environment lookup, tuple projection, allocation, copy, loop, lock,
hash, signature operation, or generic dispatch.  Mandatory inlining reduces
the source authority surface without adding a call frame.  Caching or replacing
the many discriminant probes was deliberately not attempted without production
profiles because enum construction/lifetime differs across compiler lanes.

The authoritative call census changed as follows:

- raw call sites: 19,634 -> 19,539
- lexical unsafe: 3,215 -> 3,219
- function unsafe: unchanged at 919
- missing authority: 15,500 -> 15,401

The file itself now reports four raw rows, all lexically authorized, and zero
missing authority.  Provider implementation proofs and exact signed compiler
artifacts remain absent, so verified-and-signed admission remains 0.

## Simple-core authority-coverage checkpoint

The final two simple-core gaps were `core_stdio.spl` and `core_math.spl`.
Their three ambient calls are now represented by two mandatory-inline `ffi`
owners.  The focused `simple-core-stdio-math-authority.shs` ratchet passed and
pins one-call hot paths plus both compilers' mandatory-inline recognition.

The stdio wrappers previously discarded the signed `fflush(NULL)` result and
always returned zero, fabricating success on flush failure.  They now return
the actual status with the same single foreign call.  Both functions still
flush all open output streams because this pure-core lane has no portable
stdout/stderr stream-pointer owner; it does not falsely claim stream-specific
behavior.  The square-root wrapper retains exactly one platform `sqrt` call
and unchanged IEEE/libm behavior.

The authoritative call census changed as follows:

- raw call sites: 19,635 -> 19,634
- lexical unsafe: 3,213 -> 3,215
- function unsafe: unchanged at 919
- missing authority: 15,503 -> 15,500

The same census now reports all 19 `src/runtime/simple_core/*.spl` files at
zero missing-authority sites across 244 raw-call rows.  This is an authority
coverage result, not a universal safety result: raw future-handle lifetime,
linear handle registries, single-threaded atomic fallbacks, stream identity,
provider proofs, and exact signed artifacts remain unresolved.  Production
execution and exact artifact evidence remain unavailable, so
verified-and-signed admission remains 0.

## Simple-core atomic-fallback authority checkpoint

The pure-Simple bootstrap atomic fallback retains six explicitly tagged raw
interfaces and routes all ten former ambient calls through mandatory-inline
`ffi, raw_ptr` owners.  Its eight public address/handle operations now also
declare `raw_ptr` authority: arbitrary numeric addresses and unregistered
handles cannot honestly be exposed as safe.  The allocation constructor itself
remains safe and preserves its explicit zero-on-allocation-failure contract.
The focused `simple-core-atomic-authority.shs` ratchet passed and pins the ABI
registry plus both compilers' mandatory-inline recognition.

These functions remain deliberately single-threaded bootstrap fallbacks.  The
fetch-add and compare-exchange implementations are ordinary load/conditional
store sequences and are explicitly documented as not concurrent atomic RMW
operations.  Each valid operation keeps the same number of loads, stores,
branches, and allocations; no copy, lookup, lock, hash, signature operation,
or generic dispatch was added.

The authoritative call census changed as follows:

- raw call sites: 19,639 -> 19,635
- lexical unsafe: 3,207 -> 3,213
- function unsafe: unchanged at 919 (`raw_ptr`-only owners are a separate axis)
- missing authority: 15,513 -> 15,503

Production execution and exact artifact evidence remain unavailable, so this
fallback is explicitly unsafe rather than verified; verified-and-signed
admission remains 0.

## Simple-core closure authority checkpoint

The pure-Simple closure provider retains five explicitly tagged raw
interfaces and routes all 11 former ambient calls through mandatory-inline
owners.  Allocation and pointer loads/stores require `ffi, raw_ptr`; the
fail-closed termination owner requires only `ffi`.  The focused
`simple-core-closure-authority.shs` ratchet passed and pins the pointer
intrinsics plus both compilers' mandatory-inline recognition.

The constructor still returns the raw nil sentinel for invalid function
pointers or capture counts, preserving its existing input contract.  Fixed-size
or capture-storage allocation failure is no longer conflated with that state:
it terminates through the existing abort boundary.  Successful construction
retains one allocation, the exact header/capture layout, registry link, and
bounds behavior.  No valid-path branch, allocation, copy, lookup, lock, hash,
signature operation, or generic dispatch was added.

Closure membership validation remains an O(number of live closures) intrusive
registry walk.  It avoids dereferencing arbitrary tagged integers without a
separate allocation per entry, but its scalability has no production profile;
this checkpoint therefore keeps the provider unsafe and does not claim the
registry or captured-object lifetimes verified.

The authoritative call census changed as follows:

- raw call sites: 19,645 -> 19,639
- lexical unsafe: 3,202 -> 3,207
- function unsafe: unchanged at 919
- missing authority: 15,524 -> 15,513

Production execution and exact artifact evidence remain unavailable, so
verified-and-signed admission remains 0.

## Simple-core async authority checkpoint

The pure-Simple async/future provider now tags nine raw interfaces and routes
all 11 former ambient calls through mandatory-inline owners.  Allocation,
release, and pointer loads/stores require `ffi, raw_ptr`; array operations and
termination require only `ffi`.  The focused
`simple-core-async-authority.shs` ratchet passed and pins array providers,
pointer intrinsics, and both compilers' mandatory-inline recognition.

Future allocation previously fabricated tagged `nil` on fixed-size allocation
failure.  `future_all` also ignored result-array allocation and append failure,
allowing an invalid or partial array to appear successful.  These paths now
terminate through the existing abort boundary.  Successful future construction
retains one 48-byte zeroed allocation and the same field stores.  The valid
`future_all` loop adds one unlikely append-status comparison per element; it
adds no allocation, copy, lookup, lock, hash, signature operation, or generic
dispatch.

Future handles are still accepted through a raw pointer-shape heuristic rather
than an allocation/liveness registry, and the pure-core lane deliberately does
not execute arbitrary body function pointers.  This provider therefore remains
unsafe and is not claimed as semantically complete or verified.

The authoritative call census changed as follows:

- raw call sites: 19,647 -> 19,645
- lexical unsafe: 3,193 -> 3,202
- function unsafe: unchanged at 919
- missing authority: 15,535 -> 15,524

Production execution and exact artifact evidence remain unavailable, so
verified-and-signed admission remains 0.

## Simple-core enum authority checkpoint

The pure-Simple enum provider retains six explicitly tagged raw interfaces.
All 12 former ambient call sites are now routed through mandatory-inline
owners.  Allocation and pointer loads/stores require `ffi, raw_ptr`; the
fail-closed termination owner requires only `ffi`.  The focused
`simple-core-enum-authority.shs` ratchet passed and pins the pointer intrinsics
plus both compilers' mandatory-inline recognition.

Review found that `rt_enum_new` returned tagged `nil` when its fixed 32-byte
allocation failed, fabricating absence for a constructor that promises an enum
value.  It now terminates through the existing abort boundary.  Successful
construction retains one allocation, the same field stores and registry link,
and the same representation.  No valid-path branch, allocation, copy, lookup,
lock, hash, signature operation, or generic dispatch was added.

Enum validation still performs an O(number of live enums) registry walk.  That
pre-existing bootstrap scalability ponytail is documented in the provider;
changing it without production profiles would add hash-table memory and
allocation overhead, so this checkpoint does not claim to resolve it.

The authoritative call census changed as follows:

- raw call sites: 19,653 -> 19,647
- lexical unsafe: 3,187 -> 3,193
- function unsafe: unchanged at 919
- missing authority: 15,547 -> 15,535

Production execution and exact artifact evidence remain unavailable, so
verified-and-signed admission remains 0.

## Simple-core BDD authority checkpoint

The pure-Simple native-SPipe BDD subset retains four explicitly tagged raw
interfaces.  All 13 former ambient calls are now routed through four
mandatory-inline owners; only the boxed-`u64` probe requires `ffi, raw_ptr`.
The stdout/string owners require only `ffi`.  The focused
`simple-core-bdd-authority.shs` ratchet passed and pins the providers and both
compilers' mandatory-inline recognition.

BDD pass/fail and boxed-zero state remain semantic Simple booleans.  The
truthiness path still performs one header load and only performs its payload
load after the boxed-`u64` magic matches.  Output order, counters, branches,
allocation count, and asymptotic O(1) work are unchanged; no copy, lookup,
lock, hash, signature operation, or generic dispatch was added.

The authoritative call census changed as follows:

- raw call sites: 19,662 -> 19,653
- lexical unsafe: 3,183 -> 3,187
- function unsafe: unchanged at 919
- missing authority: 15,560 -> 15,547

Production execution and exact artifact evidence remain unavailable, so
verified-and-signed admission remains 0.

## Simple-core dynamic-arithmetic authority checkpoint

The pure-Simple `Any` arithmetic layer now retains only its four used raw
interfaces; the unused `spl_f64_to_bits` declaration was removed.  All 18
former ambient calls are routed through four mandatory-inline `ffi` owners.
The focused `simple-core-any-ops-authority.shs` ratchet passed and pins the
value providers, native/interpreter bit-conversion providers, and both
compilers' mandatory-inline recognition.

The successful paths retain the same O(1) tag tests, arithmetic, projections,
and comparison results.  No branch, allocation, copy, lookup, lock, hashing,
signing, or generic dispatch was added.  Integer division/remainder by zero or
`INT64_MIN / -1` still yields integer zero in all three C, Rust, and
pure-Simple runtime lanes.  That is an established ABI behavior with no error
channel, but it also conflates invalid arithmetic with a valid result; it
requires a separate cross-lane language-contract repair and is not claimed as
verified by this authority checkpoint.

The authoritative call census changed as follows:

- raw call sites: 19,676 -> 19,662
- lexical unsafe: 3,179 -> 3,183
- function unsafe: unchanged at 919
- missing authority: 15,578 -> 15,560

Production execution and exact artifact evidence remain unavailable, so
verified-and-signed admission remains 0.

## Simple-core tagged-value authority checkpoint

The pure-Simple tagged-value layer retains eight explicitly tagged raw
interfaces.  All 20 former ambient calls are now routed through eight
mandatory-inline, minimal-capability owners: pointer allocation/load/store use
`ffi, raw_ptr`, while enum projections, float-bit conversion, and fail-closed
termination use only `ffi`.  The focused
`simple-core-values-authority.shs` ratchet passed and pins both compiler
backends' mandatory-inline recognition plus the enum providers.

Review found one fabricated-value failure path.  `rt_value_u64` previously
returned tagged `nil` when its fixed 16-byte allocation failed, even though
the function promises a lossless unsigned value.  It now terminates through
the existing abort boundary instead of manufacturing absence.  The successful
path retains the same one allocation, two stores, layout, and return encoding.
The semantic boolean interface is unchanged: callers provide full-width 0/1,
and the established true/false tags remain 11/19 across the runtime lanes.

The authoritative call census changed as follows:

- raw call sites: 19,688 -> 19,676
- lexical unsafe: 3,171 -> 3,179
- function unsafe: unchanged at 919
- missing authority: 15,598 -> 15,578

This reduces the source inventory because eight owner calls replace 20
scattered calls.  It adds no successful-path branch, allocation, copy, lookup,
lock, hashing, signing, or generic dispatch.  Production execution and exact
artifact evidence were not available, so this is static authority evidence
only; verified-and-signed admission remains 0.

Do not reuse the 2026-08-23 totals as current-tree statistics. They use an older
scanner and generous file-level unsafe attribution. Newer declaration and call
totals are also historical checkpoints with different units. The source call
census remains a lower bound until resolved-HIR inventory covers aliases,
re-exports, generated calls, methods, and indirect callables.

## Fresh source-ledger census

The repository-owned census tools were run once on this tree. These are
source-ledger measurements, not resolved-HIR ABI proof:

| Unit | Total | Unsafe tagged | Signed/admitted | Untouched |
| --- | ---: | ---: | ---: | ---: |
| `rt_*` declaration rows | 12,128 | 951 | 0 | 10,907 |
| distinct `rt_*` symbols | 3,173 | 695 | 0 | 2,246 |

Distinct `rt_*` provider-language provenance is 1,321 linked-native symbols
whose implementation language is unknown, 1,012 with no provider observed,
591 Rust symbols, and 249 C/C++ symbols.

The separate raw-call authority census found 21,757 call sites across 3,131
caller files and 3,297 called symbols. Only 1,754 sites were inside lexical
`unsafe(ffi)` and 509 inside function-level FFI authority; 19,494 lacked
explicit authority. Its ratchet failed (`19,494 > 19,412`). This scanner is a
bounded source heuristic and explicitly does not resolve aliases, re-exports,
or generated declarations; resolved HIR remains the required final authority.

### 2026-08-25 post-admission refresh

After the exact-artifact signature and typed-boolean work landed, the full
repository-owned inventory was rerun once. The distinct `rt_*` symbol total and
provider-language split were unchanged, while declaration tagging advanced:

| Unit | Total | Unsafe tagged | Signed/admitted | Untouched |
| --- | ---: | ---: | ---: | ---: |
| `rt_*` declaration rows | 12,131 | 958 | 0 | 10,901 |
| distinct `rt_*` symbols | 3,173 | 696 | 0 | 2,246 |

Distinct provider-language provenance remains 1,321 linked-native/unknown,
1,012 with no provider observed, 591 Rust, and 249 C/C++. This proves that the
tree is still not universally admitted. It also exposed 26 duplicate Simple
`rt_mkdir_p` declarations whose legacy C and canonical pointer/length provider
shapes were not one authoritative ABI. The follow-up consolidation removed all
Simple declarations and routes callers through `std.io_runtime.mkdir_p` and
its already-scoped `rt_dir_create_all` owner. The focused lint now rejects any
reintroduction. This changes neither asymptotic work nor allocation count; it
removes a duplicate boundary and an unconditional LLVM declaration.

After the subsequent sleep and current-directory consolidations, one final
full inventory run for this checkpoint reported:

| Unit | Total | Unsafe tagged | Signed/admitted | Untouched |
| --- | ---: | ---: | ---: | ---: |
| `rt_*` declaration rows | 12,070 | 963 | 0 | 10,835 |
| distinct `rt_*` symbols | 3,171 | 697 | 0 | 2,243 |

The distinct provider split is now 1,319 linked-native/unknown, 1,012 with no
provider observed, 591 Rust, and 249 C/C++. `rt_sleep_ms` no longer has a raw
Simple declaration: callers use the existing scoped `rt_thread_sleep` owner.
`rt_env_cwd` now has one hosted declaration with the truthful `text?` contract;
the total wrapper maps provider failure to `"."` and replaces the former
`pwd` subprocess. The four bootstrap-library mirrors also declare `text?` and
place calls inside lexical `unsafe(ffi)` scopes. Zero production symbols are
cryptographically admitted, so global safety and verification remain false.

### TCP descriptor/read contract checkpoint

The canonical TCP module had ambient raw calls and an impossible safety check:
`rt_io_tcp_read` returned `[u8]`, providers converted both read failure and EOF
to `[]`, and `TcpStream.read` tested `data.len() < 0`. The repaired contract is
`[u8]?`: `nil` is invalid input/provider/read failure, while `[]` is a valid
zero-length request or EOF. C, Rust runtime, and interpreter now agree, and the
Windows C fallback returns the runtime nil value rather than integer zero for
TCP text/address objects. All 20 Simple declarations use the optional contract
and every direct call is inside a one-expression `unsafe(ffi)` scope.

The source ledger after this tranche reports 12,070 `rt_*` declaration rows,
1,005 unsafe-tagged rows, 10,796 untouched rows, 3,171 distinct symbols, 720
unsafe-tagged symbols, 2,228 untouched symbols, and zero admitted production
symbols. Provider language counts remain those of the immediately preceding
full census because this tranche changes contracts, not provider ownership.

Successful TCP reads retain one provider call and the existing buffer work.
The only hot-path addition is the required predictable nil check; there is no
hash, lookup, lock, subprocess, generic dispatch, or new allocation. Focused
Rust runtime and interpreter tests each passed once, and the C runtime compile
gate compiled 118 files with zero errors (two dependency-gated skips). The
self-hosted Simple/optimizer/cross-lane gates remain unavailable and are not
claimed.

## Current enforcement boundary

- Normal and bootstrap MIR lowering now reject non-unit fallthrough with
  `E-SFFI-016`; the bootstrap change remains behaviorally unverified.
- Typed HIR identifies direct named extern calls and the safety checker finds
  calls outside lexical `unsafe(ffi)`. Default driver severity remains advisory;
  only Critical/Verified deny.
- `raw_sffi_call` remains `allow` in the default lint profile. The declaration
  and call-site ratchets freeze debt but do not verify contracts.
- The audit-only HIR inventory carries no artifact/signature evidence and cannot
  establish production admission.

## Current dynamic-provider boundary

- `ExactArtifactDynLib` provides a Linux immutable snapshot and exact digest.
- `SffiAdmissionReceiptV1` parses bounded canonical text but performs no
  cryptography and is source-forgeable.
- Evidence-bound identity checking compares provider, target, artifact, ABI
  registry, and source-signature closure, then atomically resolves cached i64
  slots. It has no production caller and does not validate loader authority.
- The standalone evidence-admission audit verifies Ed25519 trust, exact inputs,
  ABI closure, artifact symbols, and verification receipts. No compiler/runtime
  loader invokes it.
- Rust `NativeLibManager` and raw `spl_dlopen` load providers without that
  evidence gate. Production Simple callers likewise bypass manifests.
- `FfiManifest.validate_library` checks only symbol presence; it does not prove
  ABI, nullability, ownership, or signing. Its stronger cached resolvers are
  currently unused.

## Ownership and memory findings

`std.sffi.dynamic` is the canonical no-GC synchronous owner and compatibility
modules should export it. `ffi/dynamic_versioned.spl` duplicates the canonical
implementation instead of acting as a facade. `MultiVersionLoader` and
`DynLoader` retain process-global maps without eviction, so provider handles and
path text can remain live indefinitely.

Legacy dynamic calls perform per-call symbol lookup; checked integer transport
also allocates a two-element result array. Cached resolved slots remove repeated
lookup, but remain an unsafe migration ABI restricted to `i64(i64...)`.

## Performance invariant

Admission must be one-time:

```text
immutable artifact snapshot -> hash/signature/trust/ABI/receipt checks
    -> resolve complete symbol closure -> atomically publish cached typed slots
```

No admitted hot call may add hashing, signature verification, filesystem work,
path search, string lookup, dictionary lookup, generic decoding, mutex traffic,
or allocation. Required status/null/descriptor checks remain enabled.

## Statistics contract

Every future count must record tree ID, scanner identity, executable identity,
timestamp, exclusions, and exact unit. Keep these units separate:

- declarations;
- distinct symbols;
- live call sites;
- provider modules/families;
- freshly reverified cryptographic admissions.

States are mutually exclusive per row: `admitted_artifact_bound`,
`unsafe_contract_declared`, `unsafe_or_contract_missing`, and
`unknown_uninventoried`. Backed symbols, source claims, saved receipts, fixture
passes, and immutable snapshots are not “verified” or “signed.”

## Research coordination

Read-only sidecars covered compiler enforcement, library/dynload ownership, and
documentation/evidence consistency. `/root` merged and reviewed the findings.
The source-ledger censuses above were run once. The canonical release path
identified itself as the Rust bootstrap seed and the focused baseline spec
failed before execution with the already-recorded `function unsafe not found`
defect (`0.79 s`, `190,448 KiB` peak RSS). Repository policy forbids treating
that seed as self-hosted correctness or optimizer evidence, so the criterion was
not rerun and the implementation slice remains unverified.

## TCP listener checkpoint

Raw `rt_io_tcp_bind`, `rt_io_tcp_accept`, and `rt_io_tcp_accept_timeout`
declarations now state their descriptor/sentinel contracts and their direct
owned callers use one-expression `unsafe(ffi)` scopes. The timeout ABI still
conflates timeout and provider failure, so it remains explicitly unsafe rather
than being promoted to a safe typed contract. The change preserves one direct
call, the existing sentinel branch, and the existing allocation shape per site.

The post-TCP census reports 12,070 declaration rows and 3,171 distinct declared
symbols. Of those rows, 1,057 are unsafe-tagged, 754 have documented contracts,
485 are unsafe-minimized, and 10,744 remain untouched. Provider definitions are
2,378 C, 2,178 Rust, 576 Simple, and 219 C++. Cryptographically verified,
signed, and admitted rows remain zero; annotations are not admission evidence.

## TCP boolean and timeout ABI checkpoint

The TCP close, flush, shutdown, bind/listen status, and socket-option families
now use semantic `bool` in C and Rust providers and the backend boolean carrier
(`I8`) in native codegen. Timeout setters no longer reuse an incompatible
tagged `RuntimeValue`/raw-integer symbol: their raw ABI is `(i64 fd, i64 ms) ->
bool`, with non-positive milliseconds clearing the timeout. Safe Simple
wrappers retain `i64?` and lower `nil` to `-1` once before the direct call.
This removes runtime-value decoding and uses saturating millisecond-to-nanosecond
conversion; it adds no lookup, allocation, lock, or generic dispatch.

The refreshed ledger remains 12,070 rows / 3,171 symbols. Unsafe-tagged rows
increased to 1,148 and untouched rows decreased to 10,653. Contract-documented
rows remain 754 and unsafe-minimized rows remain 485 because source annotations
alone are not executable admission contracts. Verified-and-signed rows remain
zero.

## Executable reason-contract census checkpoint

The inventory now recognizes explicit unsafe reason clauses such as `false
means close failed`, `negative ... means failure`, nil/empty distinctions, and
socket-family mappings as documented contracts. This changes only debt
classification: it does not create evidence, verify a signature, or admit an
artifact. A unit fixture proves a false-status reason is documented while its
cryptographic admission and evidence remain absent.

After TCP connect/accept/family hardening and removal of the dormant fabricated
C bind provider, the ledger is 12,070 rows / 3,171 symbols: 1,163 unsafe-tagged,
883 contract-documented, 614 unsafe-minimized, and 10,638 untouched. Provider
definitions are C 2,377, Rust 2,178, Simple 576, and C++ 219. Verified-and-signed
remains zero.

## Bootstrap shell raw-contract checkpoint

All 25 filesystem, environment, process, path, search, and directory externs in
the bootstrap shell module now carry adjacent operation-specific `unsafe(ffi)`
metadata. Contracts identify ambiguous empty file/path/list values, recursive
filesystem effects, captured process output and launch failure, target-owned
path text, and process-environment mutation.

`rt_env_get` is now correctly optional and `env.get` applies its default only
to `None`, not to a legitimate empty environment value. This preserves the same
single environment lookup and removes the fabricated equivalence between
missing and empty. No filesystem scan, process launch, output capture,
allocation, copy, environment read, branch beyond the existing default choice,
or generic dispatch was added. A static ratchet fixes all declarations and the
optional lookup contract.

Estimated declaration totals remain 11,651 / 3,137 symbols. Unsafe-tagged rows
increase from 2,154 to 2,178, untouched rows decrease from 9,302 to 9,278, and
exact-artifact verified-and-signed admission remains zero.

## Bootstrap math ABI-conflict checkpoint

The bootstrap core math module declares 24 `rt_math_*` functions with `f32`
parameters/results, but the canonical Rust runtime exports those exact symbol
names with `f64` ABIs. This is an ABI conflict on native lanes, not a numerical
precision preference. Changing the shared provider to `f32` would break the
canonical `f64` API; widening the bootstrap public API would also be an
incompatible workaround.

Every bootstrap declaration now explicitly records the conflict as
`unsafe(ffi)`. A static ratchet fixes both sides while the correct solution is
implemented: generated `_f32` provider symbols and typed direct thunks, with
both signature families in the ABI registry. That solution preserves the
public `f32` API and adds no allocation, boxing, lookup, conversion loop, or
generic dispatch. The current annotation pass changes no math call, branch,
conversion, result, or memory behavior and does not claim verification.

Estimated declaration totals remain 11,651 / 3,137 symbols. Unsafe-tagged rows
increase from 2,178 to 2,202, untouched rows decrease from 9,278 to 9,254, and
exact-artifact verified-and-signed admission remains zero.

## UDP scalar-option ABI checkpoint

The UDP `connect`, `set_broadcast`, `set_read_timeout`, and `set_nonblocking`
family now uses one Simple-facing contract across the C provider, Rust provider,
interpreter registry, and native-codegen registry. Status values are semantic
`bool`; the optional timeout is lowered once by the safe Simple wrapper to an
`i64` millisecond value with `-1` meaning no timeout. Interpreter entry points
reject non-boolean/non-scalar bridge values instead of applying truthiness or a
default. The benchmark caller now stops if nonblocking setup fails rather than
silently running a blocking workload.

The hot path remains constant-time and allocation-free beyond the provider's
existing socket-registry lookup: there is no hashing, signature verification,
symbol/name lookup, generic marshalling, heap allocation, or data copy per
option call. Focused evidence passed: the C translation-unit syntax check, 3
Rust runtime contract tests, 8 compiler interpreter/codegen tests, and the
cross-lane SFFI signature ratchet. The canonical self-hosted optimizer was not
run because the repository still records the admitted Stage-4 runtime as
blocked; the Rust seed was not substituted.

A fresh source-only census reports 12,038 `rt_*` declaration rows and 3,179
distinct `rt_*` symbols. Of the rows, 1,187 are unsafe-tagged, 562 have an
executable reason contract and minimal unsafe scope, 10,581 remain untouched,
and zero are exact-artifact verified-and-signed. Source-only mode deliberately
reports provider language as `none_observed`; the older C/Rust/Simple/C++
provider counts are not reused as if they described this changed revision.

## UDP data-path null/empty and ownership checkpoint

The UDP data path now distinguishes a valid zero-length datagram from provider
failure in every implemented lane. `rt_io_udp_recv` returns `[u8]?` and
`rt_io_udp_recv_from` returns `([u8], text)?`: `nil` means invalid input,
`WouldBlock`, or provider failure, while a present empty array means an actual
zero-length datagram. Send operations return a negative status on invalid input
or provider failure; zero remains the valid length of an empty datagram. Receive
sizes outside `0..65535` fail before allocation or system I/O.

The C and Rust providers allocate one packed runtime byte buffer and receive
directly into it. Every failed receive frees that buffer. Rust peer-address
formatting uses a fixed 64-byte stack buffer and only the required runtime text
allocation; it does not create an intermediate `String`. The benchmark now uses
the connected-shape receive API when it intentionally discards the peer address,
so it avoids tuple/text allocation and correctly counts zero-length datagrams.
A static ratchet rejects payload copies, intermediate collections/strings,
hashing, dynamic lookup, and new registry types in the Rust data wrapper.

Focused evidence passed: C syntax, 5 runtime tests including a real loopback
zero-length datagram, 11 compiler interpreter/codegen tests, mirrored benchmark
parity, and the cross-lane SFFI ratchet. The refreshed source-only ledger is
12,038 `rt_*` declaration rows / 3,179 symbols: 1,200 unsafe-tagged, 568
contract-documented and unsafe-minimized, 10,572 untouched, and zero
exact-artifact verified-and-signed.

## Common ECDSA P-256 checked-result checkpoint

`std.common.crypto.ecdsa_p256` no longer calls the legacy signing and
verification ABIs that collapse bridge failures into an empty signature or
`false`. Signing now returns `Result<[u8], text>` and accepts only a two-field
checked descriptor with status zero and an exactly 64-byte signature.
Verification returns `Result<bool, text>`: a genuine mismatch is `Ok(false)`,
while malformed SPKI/signature shapes, corrupt statuses, and bridge failures
are `Err`. The typed wrapper propagates the result instead of constructing
`Signature.new([])`.

Both common and canonical signature wrappers put each checked raw call in a
one-statement lexical `unsafe(capabilities: [ffi])` scope. No hashing, symbol or
map lookup, input conversion, payload copy, or provider allocation was added.
The focused static guard and two-file source check passed. The executable crypto
spec is blocked before this module by an unrelated parser error in
`src/app/io/env_access_host.spl` (`expected Comma, found Pub`). The available
binary also identifies itself as the Rust bootstrap seed, so it is not accepted
as self-hosted verification.

The refreshed source-only ledger remains 12,038 `rt_*` declaration rows and
3,179 symbols: 1,202 rows are unsafe-tagged, 650 are in
`unsafe_contract_declared`, 10,570 are untouched, and zero are exact-artifact
verified-and-signed.

## P-384/P-521 unresolved-provider removal checkpoint

The four advertised `rt_ecdsa_p{384,521}_{sign,verify}` declarations had no C
or Rust implementation, interpreter registration, or typed codegen entry. They
could therefore only fail resolution or be replaced by a fabricated weak/stub
result. They are now removed from the sync and async signature facades. The SSH
host-key dispatcher returns `Result<bool, text>` and reports that these
algorithms require their canonical pure-Simple providers instead of mapping
provider absence to `false`.

The working P-384/P-521 implementations remain the pure-Simple
`os.crypto.p384` and `os.crypto.ecdsa_p521` engines already used by TLS. This
removal eliminates foreign dispatch and cannot add hot-path hashing, lookup,
allocation, or copying. A static ratchet rejects reintroduction of any of the
four raw declarations and asserts that both pure-Simple sign/verify owners
remain present. The ratchet and focused two-module source check passed; the
available executable still identifies itself as a bootstrap seed and is not
accepted as self-hosted verification.

Removing the nonexistent APIs changes the source-only ledger to 12,034 `rt_*`
declaration rows and 3,175 symbols: 1,198 rows are unsafe-tagged, 646 are in
`unsafe_contract_declared`, 10,570 are untouched, and zero are exact-artifact
verified-and-signed.

## SSH session crypto-authority reduction checkpoint

The SSH session and helper modules declared raw RSA-SHA256 and Ed25519 verify
externs that they never called. Those three declarations are removed. A static
ratchet prevents these session modules from reacquiring direct signature
verification authority; verification belongs to the checked signature owner.
This is a pure surface reduction with no runtime branch, allocation, copy,
lookup, hashing, or dispatch change. The ratchet and focused two-module source
check passed, while the available executable still identifies itself as the
bootstrap seed rather than admitted self-hosted evidence.

The source-only ledger is now 12,031 `rt_*` declaration rows / 3,175 symbols:
1,198 rows unsafe-tagged, 646 `unsafe_contract_declared`, 10,567 untouched, and
zero exact-artifact verified-and-signed.

## Canonical signature facade checked-result checkpoint

The canonical no-GC signature facade no longer declares the eight legacy
RSA-SHA256, RSA-SHA512, Ed25519, and ECDSA-P256 sign/verify entry points. Its
existing public names now return `Result` and delegate to the corresponding
checked provider contracts. A genuine verification mismatch remains
`Ok(false)`; malformed arrays, private keys, signature shapes, corrupt result
descriptors, and provider signing failure are typed errors. Signing can no
longer expose an empty array as a successful value.

Primary compiler, TLS, Ed25519, and cross-provider specs were updated so
positive vectors unwrap checked results and malformed cases assert `Err`.
Production TLS/package consumers already used the checked names. The change
performs the same one cryptographic provider call and adds only bounded status,
descriptor-length, and signature-length checks. It adds no per-call hash beyond
the algorithm itself, symbol lookup, map lookup, generic dispatch, input copy,
or provider allocation.

The static ratchet and facade source check passed. Executable SSpec remains
blocked before the target spec by the unrelated parser error in
`src/app/io/env_access_host.spl`; the available binary also identifies itself
as the bootstrap seed. The source-only ledger is now 12,023 `rt_*` declaration
rows / 3,172 symbols: 1,190 tagged, 638 `unsafe_contract_declared`, 10,567
untouched, and zero exact-artifact verified-and-signed.

## OS ECDSA P-256 result-propagation checkpoint

`os.crypto.ecdsa_p256` no longer imports the deleted raw runtime symbols. Its
fixed-width sign and verify APIs consume the checked facade and return
`Result`. TLS maps provider errors separately from cryptographic mismatch, SSH
and JWT propagate errors, and COSE sign/verify dispatch now carries typed
`CoseError` values rather than returning an empty signature or `false` for an
unavailable/malformed provider result.

The data path still performs exactly one provider cryptographic call. The
change adds only bounded result/status matching and removes sentinel tests; it
adds no lookup, hashing beyond ECDSA itself, payload copy, allocation, or
generic dispatch. The static guard and all six production-module source checks
passed. The TLS verifier's unsupported compact unit-variant pattern was
replaced by an explicit total match, removing that parser blocker. The
available binary remains a bootstrap seed, not admitted self-hosted proof.
Both P-256 spec mirrors are byte-identical; the TLS mirror's pre-existing
placeholder assertions were replaced by the canonical real value/error checks.

No declaration was added or removed in this propagation tranche, so the
source-only ledger remains 12,023 `rt_*` rows / 3,172 symbols: 1,190 tagged,
638 `unsafe_contract_declared`, 10,567 untouched, and zero exact-artifact
verified-and-signed.

## OS RSA typed-result checkpoint

`os.crypto.rsa` no longer redeclares or directly calls the four legacy
RSA SHA-256/SHA-512 sign/verify runtime symbols. It consumes the canonical
checked signature facade, exposes `Result` from signing and verification, and
JWT now propagates provider/malformed-input errors instead of interpreting an
empty signature or verification bridge failure as a cryptographic result.
The mirrored RSA specs assert `Ok(true)`, `Ok(false)`, and typed failures.

The normal automatic signing path still makes exactly one hosted provider call
on success and invokes the Pure Simple fallback only after a typed hosted
failure. Comparison modes retain their intentional two-engine behavior. There
is no new lookup, hash beyond RSA itself, payload copy, generic dispatch, or
success-path error allocation; failure text is allocated only on failure.

The focused static checked-caller ratchet passed. The production source-check
gate refused the only available executable because it identifies as a
non-production bootstrap runtime, so this tranche is not executable-verified
or artifact-admitted. The full census run was stopped after it emitted its
large inventory without converging; the exact declaration delta is four rows
removed and no rows added. Applied to the preceding ledger, the source-only
count is 12,019 `rt_*` declaration rows / 3,172 symbols: 1,190 tagged, 638
`unsafe_contract_declared`, 10,563 untouched, and zero exact-artifact
verified-and-signed.

## Ed25519 seed-signing canonical-owner checkpoint

The optional `rt_ed25519_sign_seed` ABI now has one canonical declaration and
a checked wrapper in `signature_sffi`. The wrapper rejects invalid seed/public
key lengths before dispatch, requires a present 64-byte signature afterward,
and returns typed provider/contract errors. `os.crypto.ed25519` no longer owns
or calls the raw symbol, and its previously inconsistent `ed25519_sign_live`
API now returns `Result` throughout instead of treating a runtime `Result` as
an array or falling back to an empty public result.

The live runtime path retains its existing diagnostic schedule: one direct
seed-sign provider call plus its component-runtime comparison. Normal
Pure-Simple-first and runtime-first selection retain their previous ordering;
no lookup, payload copy, hash beyond Ed25519 itself, generic dispatch, or
success-path error allocation was added. The focused static ratchet passed.
The policy-accepted production runtime remains unavailable, so executable
verification and signed admission remain open.

This change relocates rather than adds/removes the one declaration, so the
ledger remains 12,019 rows / 3,172 symbols, 1,190 tagged, 638
`unsafe_contract_declared`, 10,563 untouched, and zero exact-artifact
verified-and-signed.

## Common P-256 canonical-owner checkpoint

`std.common.crypto.ecdsa_p256` now imports the canonical checked signature
facade instead of redeclaring the P-256 sign and verify providers. Its existing
SPKI-to-raw-point validation and exact 64-byte signature contract remain local.
The shared verification lift now also rejects provider statuses above `1`, so
unknown statuses cannot be converted to `Ok(false)`.

The sign and verify hot paths still make one provider call. The migration adds
no lookup, copy, allocation, hashing beyond ECDSA itself, or generic dispatch;
it removes duplicate unsafe declarations and their local descriptor decoder.
The focused static ratchet passed. Production source checking remains blocked
by the policy-rejected bootstrap executable recorded above, so this is not
artifact admission. The exact declaration delta is two tagged rows removed and
none added: 12,017 rows / 3,172 symbols, 1,188 tagged, 636
`unsafe_contract_declared`, 10,563 untouched, and zero exact-artifact
verified-and-signed.

## General crypto unresolved-provider removal checkpoint

The general crypto facade advertised 17 raw symbols, duplicated again by
`app.io.crypto_ffi`. A provider search across Rust runtime/compiler and C
runtime sources found an implementation only for `rt_random_hex`; the other 16
hash/HMAC/password/AES/key/PBKDF2/random-byte symbols had no implementation.
The app module is now a zero-cost re-export. The canonical facade routes
SHA-256/SHA-512/SHA3-256/BLAKE3 and HMAC-SHA256/SHA512 to existing in-tree
owners, removes the unsupported password/AES/key/PBKDF2 advertisements, and
keeps only `rt_random_hex` under one lexical `unsafe(ffi)` wrapper with
presence, exact-length, lowercase-hex, and nonzero-entropy validation.
The async compatibility facade now exports only this supported surface, so it
cannot keep the removed provider names alive through another module path.

The supported algorithms remain linear in input length. CSPRNG remains one
provider call plus its existing linear output validation. No lookup, retry,
generic dispatch, or extra entropy buffer was added. Hash/HMAC previously had
no callable provider, so routing them to Pure Simple changes an unresolved
operation into a real implementation rather than regressing an executable
baseline. Existing entropy failure specs and crypto vector suites remain the
correctness coverage. The focused static ratchet passed; production execution
is still blocked by the policy-rejected bootstrap runtime.

Thirty-three declaration rows and sixteen unsupported symbol identities are
removed. The source-only ledger is now 11,984 rows / 3,156 symbols: 1,189
tagged, 637 `unsafe_contract_declared`, 10,529 untouched, and zero
exact-artifact verified-and-signed.

## Web session-token entropy-owner checkpoint

`app.ui.web.session_token` no longer redeclares or directly calls
`rt_random_hex`. Token IDs and development-secret entropy use the canonical
checked CSPRNG facade, which preserves the existing fail-closed unwrap while
also rejecting missing, wrong-length, non-lowercase-hex, or all-zero output.
Issuance still performs exactly one provider call. The additional validation
is one bounded linear scan (64 characters for a token ID, 16 for the current
development-secret request) with no copy, lookup, retry, or allocation.

The focused static ratchet passed. Production execution remains blocked by the
policy-rejected bootstrap runtime, and exact-artifact admission remains zero.
One duplicate declaration row is removed: 11,983 rows / 3,156 symbols, 1,189
tagged, 637 `unsafe_contract_declared`, 10,528 untouched, and zero signed.

## Credential-store entropy-owner checkpoint

Credential key-salt and AES-CBC IV generation now use the canonical checked
CSPRNG owner instead of a local `rt_random_hex` declaration. Both paths retain
their existing nullable fail-closed behavior and exactly one provider call per
fresh salt or IV. Canonical validation adds only bounded scans of the returned
32-character strings and no copy, lookup, retry, or allocation. The existing
JIT re-materialization workaround remains untouched after validation.

The focused static ratchet passed; executable and signed-artifact admission
remain unavailable. One declaration row is removed: 11,982 rows / 3,156
symbols, 1,189 tagged, 637 `unsafe_contract_declared`, 10,527 untouched, and
zero exact-artifact verified-and-signed.

## WebSocket entropy-result checkpoint

Browser WebSocket handshake keys and client-frame masks now use canonical
checked entropy. The local non-null `rt_random_hex` declaration is removed;
both generators return browser `Result`, and the connect/send/receive-control/
close/ping callers propagate failure before emitting an unmasked or predictable
frame. Success performs exactly one CSPRNG call and the existing counter mix.
Validation scans only 32 handshake-key hex characters or 8 mask characters;
there is no retry, lookup, generic dispatch, or additional entropy buffer.

The focused static ratchet passed. Production execution and signed admission
remain blocked as recorded above. One declaration row is removed: 11,981 rows
/ 3,156 symbols, 1,189 tagged, 637 `unsafe_contract_declared`, 10,526
untouched, and zero exact-artifact verified-and-signed.

## OAuth entropy-result checkpoint

The no-GC sync, no-GC async, and GC async OAuth variants no longer redeclare
or call `rt_random_hex`, and they no longer substitute `"0"` when entropy is
unavailable. `random_int`, random-string generation, CSRF state, timestamped
state, PKCE verifier, and mock-token creation now return and propagate typed
`Result` failures. The OAuth entropy spec uses the canonical checked facade
rather than bypassing it with another raw declaration.

Success retains the previous one CSPRNG draw per generated character and stops
immediately on failure. Each draw now includes the canonical bounded
16-character validation scan; there is no retry, payload copy, lookup, generic
dispatch, or added random draw. The focused static ratchet passed. Production
execution and exact-artifact admission remain unavailable.

Three declaration rows are removed: 11,978 rows / 3,156 symbols, 1,189 tagged,
637 `unsafe_contract_declared`, 10,523 untouched, and zero exact-artifact
verified-and-signed.

## Security correlation-ID entropy checkpoint

`security.types` no longer redeclares `rt_random_hex` or converts missing
entropy to an empty suffix. Correlation IDs use the canonical checked owner and
fail closed on nil/malformed/all-zero entropy, preserving the existing `text`
constructor API without fabricating a timestamp-only identifier. Across the
repository, `rt_random_hex` now has exactly one declaration and one lexical
call, both in the canonical crypto facade.

The success path remains one provider call plus a bounded 16-character scan,
with no copy, retry, lookup, generic dispatch, or allocation added. The static
ratchet passed. Production execution and signed admission remain unavailable.
One declaration row is removed: 11,977 rows / 3,156 symbols, 1,189 tagged, 637
`unsafe_contract_declared`, 10,522 untouched, and zero exact-artifact
verified-and-signed.

## Application TLS facade consolidation checkpoint

`app.io.tls_sffi` was a second copy of the canonical TLS module: the same 35
raw declarations and wrappers, differing only because the application copy did
not export its surface directly. It is now a compatibility re-export of
`std.nogc_sync_mut.io.tls_sffi`, and `app.io.tls_ffi` continues to select its
named safe facade from that path.

This is a zero-runtime-cost consolidation: no TLS provider call, branch,
allocation, copy, lookup, or handshake behavior changes. The focused TLS
fail-closed/static-owner ratchet passed. Production execution and signed
admission remain unavailable. Thirty-five duplicate declaration rows are
removed: 11,942 rows / 3,156 symbols, 1,189 tagged, 637
`unsafe_contract_declared`, 10,487 untouched, and zero exact-artifact
verified-and-signed.

## TLS-disabled native provider removal checkpoint

The Rust runtime previously included `net_tls_stub.rs` whenever `runtime-tls`
was disabled. That file exported the full TLS symbol family while returning
`-1`, empty text, or `false`; in particular, a missing provider read was
indistinguishable from clean EOF. The stub module is deleted, its include is
removed, and TLS re-exports from both runtime layers are gated by the real
`runtime-tls` feature. A TLS-disabled runtime can still build, but an artifact
requiring TLS now fails linkage/admission instead of receiving fabricated
values.

The TLS-enabled implementation is unchanged, so there is no added branch,
lookup, allocation, copy, or call overhead. `cargo check` passed once for both
`--no-default-features` and `--no-default-features --features runtime-tls`.
The TLS static fail-closed ratchet also passed. This changes provider behavior,
not Simple declaration inventory, so the ledger remains 11,942 rows / 3,156
symbols, 1,189 tagged, 637 `unsafe_contract_declared`, 10,487 untouched, and
zero exact-artifact verified-and-signed.

## TLS client checked-read checkpoint

The rustls client provider previously returned empty text for invalid input,
unknown handles, socket-timeout setup failure, read failure, and clean EOF.
`rt_tls_client_read_checked` now returns `nil` for the failure cases while
retaining empty text for clean EOF. The web TLS client consumes that nullable
contract and maps only `nil` to `Result.Err`; legitimate empty reads remain
`Result.Ok("")`. The legacy symbol remains available for unmigrated callers.

Both entry points share one implementation. The checked success path keeps one
handle lookup, one bounded buffer allocation, one socket read, and one text
lift; it adds no descriptor, copy, retry, generic dispatch, or symbol lookup.
The legacy path adds only a failure-path conversion to its historical empty
sentinel. The TLS static ratchet, both runtime feature compile checks, and the
focused runtime and interpreter bridge tests passed. The compiler now selects
the real `runtime-tls` provider explicitly, and its compile check passed; this
prevents fake-stub removal from leaving registered interpreter handlers without
implementations. Rust formatting remains WARN
because unrelated `wsffi_native.rs` and surrounding export lists were already
not rustfmt-clean; they were not absorbed into this lane.

One tagged declaration/symbol is added for the checked ABI: 11,943 rows / 3,157
symbols, 1,190 tagged, 638 `unsafe_contract_declared`, 10,487 untouched, and
zero exact-artifact verified-and-signed. The broader TLS/SFFI surface remains
unsafe and unadmitted.

## TLS server checked-read checkpoint

The rustls server read now has the same explicit three-state contract as the
client: checked failure is `nil`, clean EOF is empty text, and data is nonempty
text. Hosted legacy and checked symbols share one inlineable implementation;
the compile-time checked flag is consulted only on failure paths. Successful
reads retain one handle lookup, one bounded buffer allocation, one socket read,
and one text lift with no added copy, descriptor, retry, lookup, or dispatch.

The web serve loop now imports the checked canonical declaration, reports I/O
failure separately from EOF, and no longer redeclares the byte-write provider.
The canonical friendly server-read wrapper is `Result<text,text>` and cannot
manufacture empty text for an invalid handle. SimpleOS exports the same checked
symbol and returns `nil` because its live netstack provider is unavailable.

The focused static audit and hosted client/server failure-identity test passed.
Production Simple checking remains unavailable under the repository runtime
policy and was not replaced with a seed run. Adding one canonical tagged
declaration while deleting one application duplicate keeps 11,943 declaration
rows; there are now 3,158 symbols, 1,191 tagged declarations, 639
`unsafe_contract_declared`, 10,486 untouched, and zero exact-artifact
verified-and-signed.

## TLS accept/write/close typed-wrapper checkpoint

The hosted provider already reports accept/write failure with a negative i64
and close outcome with a semantic boolean. No replacement numeric convention
or second provider ABI was needed. The canonical client write/read/close and
server accept/write/read/close wrappers now return typed `Result` values rather
than manufacturing zero, false, empty text, or an invalid resource object.
The mail and web-server callers propagate or explicitly handle those results.

Web accept/write/close helpers retain one provider call and move their existing
status branch into the helper. `Result.Ok` carries the existing scalar/resource
directly; no payload copy, retry, lookup, descriptor, generic dispatch, or heap
buffer was introduced. The Rust provider is unchanged. The canonical raw
accept/write/read/close declarations now carry minimal `unsafe(ffi)` contract
tags, and the previously missing canonical byte-write declaration replaces the
application-local duplicate removed in the preceding slice.

The focused static gate passed. Production Simple checking and optimizer
evidence remain unavailable under the repository runtime policy. The estimate
is now 11,944 declaration rows / 3,158 symbols, 1,199 tagged declarations, 647
`unsafe_contract_declared`, 10,479 untouched, and zero exact-artifact
verified-and-signed.

## TLS constructor and shutdown typed-wrapper checkpoint

Canonical client connect/SNI connect and server create no longer return invalid
resource objects on provider failure; they return typed `Result` values.
Server shutdown similarly maps the provider's semantic boolean to `Result<()>`
instead of exposing false as an ambiguous safe outcome. Mail and web startup
callers now pattern-match those results. Raw provider semantics remain negative
handle sentinels and boolean shutdown status; no boolean was converted to an
integer and no new ABI was introduced.

Each success path still performs one provider call and its existing handle or
boolean branch. Result construction adds no payload copy, retry, lookup,
descriptor, generic dispatch, or foreign allocation. The four raw constructor/
shutdown declarations now carry minimal `unsafe(ffi)` contract tags. The
focused static ratchet passed; production Simple/optimizer evidence remains
unavailable under policy.

The estimate remains 11,944 declaration rows / 3,158 symbols, with 1,203 tagged
declarations, 651 `unsafe_contract_declared`, 10,475 untouched, and zero
exact-artifact verified-and-signed.

## Fabricated TLS configuration provider removal checkpoint

The six client-configuration and four server-configuration symbols had no
callers and no provider state. Hosted implementations returned synthetic
handles or unconditional `true`; SimpleOS exported corresponding unavailable
stubs. All ten symbols are now removed from the canonical facade, hosted
provider exports, compiler runtime-symbol registry, and SimpleOS.

Removal is preferable to an unused compatibility subsystem: it eliminates
advertised false capability and adds no handle table, allocation, lock, lookup,
branch, or release path. The static absence ratchet passed, and both TLS-disabled
and TLS-enabled runtime compile checks passed once.

The estimate falls to 11,934 declaration rows / 3,148 symbols, with 1,203
tagged declarations, 651 `unsafe_contract_declared`, 10,465 untouched, and
zero exact-artifact verified-and-signed.

## Fabricated TLS certificate provider removal checkpoint

Ten unused certificate/peer/self-sign/hash symbols were advertised without an
implementation: hosted code returned synthetic handles, empty metadata,
unconditional release success, or guaranteed failure, while SimpleOS exported
equivalent unavailable stubs. They are removed from the canonical facade,
hosted exports, compiler runtime registry, and SimpleOS. The now-unused atomic
fake-handle generator is also removed. Application, async, and library-root
compatibility facades no longer re-export the removed types or functions.

Connection info no longer calls a fabricated peer-certificate handle path;
`peer_cert_subject` is explicitly optional and currently `nil`. Removing these
paths reduces code and static state and introduces no provider call, allocation,
lock, lookup, branch, or dispatch. The static absence ratchet and both runtime
feature compile configurations passed once.

The estimate falls to 11,924 declaration rows / 3,138 symbols, with 1,203
tagged declarations, 651 `unsafe_contract_declared`, 10,455 untouched, and
zero exact-artifact verified-and-signed.

## Truthful TLS connection metadata checkpoint

Protocol, cipher, ALPN, and handshake providers no longer fabricate `"tcp"`,
empty cipher metadata, or unconditional `true`. Invalid/stale/incomplete
connections return `nil`; ALPN uses empty text only for the valid ordinary
"not negotiated" outcome. Handshake presence is optional while its contained
value remains a semantic boolean. Canonical safe wrappers lift metadata and
handshake state into typed `Result` values, and browser/interpreter callers
handle absence explicitly.

Cipher names are selected from static literals for the rustls ring-supported
suites. The provider performs no `format!`, temporary `String`, or second text
copy. Existing table lookup/lock count and provider-call count are unchanged;
each returned text uses the existing single runtime text lift. The static
ratchet, compiler check, and focused invalid-handle metadata test passed.

Declaration and symbol totals remain 11,924 / 3,138. Five formerly untagged
raw declarations are now minimally `unsafe(ffi)`: 1,208 tagged declarations,
656 `unsafe_contract_declared`, 10,450 untouched, and zero exact-artifact
verified-and-signed.

## Browser TLS canonical checked-owner checkpoint

`browser_net_runtime` no longer redeclares TLS providers. It imports the
canonical owner and uses checked nullable reads plus the real address-connect,
write, and checked-read timeout ABIs. The previous branches ignored every
timeout and called the non-timeout provider in both arms; they are removed.
Browser transport helpers and `TlsConnection` now return typed `Result` values
for connect/read/write/close, preserving empty text as clean EOF.

Each operation performs exactly one provider call. There is no retry, timer
task, generic lookup, second buffer, or payload copy. Checked timeout read uses
the same internal single-read implementation as the other client reads. The
static owner/timeout ratchet, compiler integration check, and focused checked
read test passed.

Adding three canonical timeout declarations, removing five browser-local TLS
declarations, and adding two non-TLS raw authority tags yields an estimated
11,922 declaration rows / 3,139 symbols, 1,212 tagged declarations, 660
`unsafe_contract_declared`, 10,446 untouched, and zero exact-artifact
verified-and-signed.

## Ambiguous TLS read provider removal checkpoint

After browser migration, no Simple caller remained for legacy client read,
client timeout-read, or server read. Those three providers are removed from
hosted exports, interpreter registration, native symbol tables, canonical
declarations, and SimpleOS. Only nullable checked reads remain. SimpleOS now
also exports fail-closed checked client read/timeout and the real timeout symbol
family required by sealed consumers.

This deletion reduces code and dispatch surface. It adds no compatibility
branch, lookup, allocation, copy, or provider call. The static checked-only
ratchet, compiler integration check, and focused invalid-handle read test
passed; only pre-existing compiler warnings remain.

Removing two canonical declarations and three unique symbols yields an
estimated 11,920 declaration rows / 3,136 symbols, 1,210 tagged declarations,
658 `unsafe_contract_declared`, 10,446 untouched, and zero exact-artifact
verified-and-signed.

## Graphics2D canonical-owner consolidation checkpoint

`app.io.graphics2d_sffi` duplicated the full 510-line canonical module and its
49 `rt_lyon_*` declarations. Its only semantic difference was weaker handle
validation: it accepted every negative handle as valid via `handle != 0`, while
the canonical owner requires `handle > 0`. The application module is now a
two-line compatibility re-export of `std.nogc_sync_mut.io.graphics2d_sffi`.

This removes duplicate declarations and the negative-handle divergence with no
runtime call, branch, allocation, copy, lookup, or layout change. A dedicated
owner ratchet requires exactly 49 declarations in the canonical file and
forbids providers, wrappers, or `handle != 0` semantics in the application
facade; it passed.

Based on the authoritative inventory immediately before this consolidation,
the estimate is 11,870 `rt_*` declaration rows / 3,135 symbols, 1,210 tagged,
10,402 untouched, and zero exact-artifact verified-and-signed.

## Graphics2D raw-contract ownership checkpoint

All 49 declarations in the canonical Lyon owner now carry an adjacent,
operation-specific `@unsafe(... capabilities: [ffi])` contract. The annotations
identify handle, tuple, array, text, count, and failure-sentinel ABI families;
they do not claim semantic verification or signed-artifact admission. The owner
ratchet now requires all 49 declarations to remain explicitly tagged.

This is compile-time metadata only. It changes no foreign signature, wrapper,
branch, lookup, allocation, copy, data layout, or provider call. The owner
ratchet and diff whitespace check passed. The unavailable production
self-hosted runtime means no new Simple compiler or optimizer claim is made.

Relative to the preceding authoritative inventory, totals remain 11,870
`rt_*` declaration rows / 3,135 symbols. Unsafe-tagged rows increase from 1,210
to 1,259, untouched rows decrease from 10,402 to 10,353, and exact-artifact
verified-and-signed admission remains zero. The existing wrappers still encode
some invalid-handle failures as dummy resources, zeros, empty arrays, or
booleans; those APIs require typed failure migration before they can be called
safe.

## SIMD raw-contract ownership checkpoint

The canonical SIMD module's 49 raw declarations now carry adjacent
`@unsafe(... capabilities: [ffi])` contracts. The contracts distinguish target
feature queries, profile discriminants and text, mutable bulk array copying,
fixed-width vector operations, shifts, fused operations, and reductions. A new
static ratchet fixes the reviewed inventory at 49 and requires every declaration
to retain its FFI capability tag.

This pass deliberately does not wrap or redirect an intrinsic: no signature,
dispatch tier, call count, branch, allocation, copy, vector layout, or fallback
behavior changed. That preserves the SIMD hot path and avoids laundering an ABI
boundary into a slower generic adapter. The static ratchet and whitespace check
passed; no production-runtime or optimizer claim is made while the self-hosted
runtime remains unavailable.

Totals remain 11,870 `rt_*` declaration rows / 3,135 symbols. Unsafe-tagged
rows increase from 1,259 to 1,308, untouched rows decrease from 10,353 to
10,304, and exact-artifact verified-and-signed admission remains zero. These
annotations identify unsafe ownership only; exact target ABI fingerprints and
signed provider admission are still required before SIMD can be called fully
verified.

## Rapier2D canonical-owner consolidation checkpoint

`app.io.rapier2d_sffi` duplicated the canonical 472-line Rapier2D wrapper and
all 48 `rt_rapier2d_*` declarations. The app copy's only semantic divergence
was weaker validation at nine resource-construction sites: `handle != 0`
accepted negative provider error sentinels, while the canonical library owner
requires `handle > 0`. The app module is now a two-line compatibility re-export
of `std.nogc_sync_mut.io.rapier2d_sffi`.

This removes a duplicate foreign boundary and selects the stricter existing
semantics. It adds no runtime call, branch, lookup, allocation, copy, or layout
change. A static owner ratchet requires exactly 48 declarations in the
canonical owner and forbids declarations, wrappers, or negative-handle
acceptance in the app facade; it passed with the whitespace check.

Totals decrease from 11,870 to 11,822 `rt_*` declaration rows while unique
symbols remain 3,135. Unsafe-tagged rows remain 1,308, untouched rows decrease
from 10,304 to 10,256, and exact-artifact verified-and-signed admission remains
zero. The canonical Rapier2D declarations and fallible wrapper returns still
need contract tagging and typed-error review.

## Rapier2D raw-contract ownership checkpoint

All 48 declarations in the canonical Rapier2D owner now carry adjacent,
operation-specific `@unsafe(... capabilities: [ffi])` contracts. The metadata
identifies world, body, collider, contact-list, and joint handle families;
tuple, tagged-tuple, array, scalar/count, boolean-status, and error-text return
families; and the nonpositive or negative failure sentinels where applicable.
The owner ratchet now requires all 48 declarations to remain explicitly tagged.

This changes no foreign signature, wrapper, call count, dispatch, branch,
allocation, copy, or resource layout. The physics simulation and query hot
paths remain direct. The static owner ratchet and whitespace check passed; no
production-runtime or optimizer claim is made while the self-hosted runtime is
unavailable.

Totals remain 11,822 `rt_*` declaration rows / 3,135 symbols. Unsafe-tagged
rows increase from 1,308 to 1,356, untouched rows decrease from 10,256 to
10,208, and exact-artifact verified-and-signed admission remains zero. The raw
tags identify the unsafe boundary but do not make dummy-resource, zero-tuple,
or boolean failure wrappers typed or verified.

## Metal symbol-identity collision checkpoint

Metal review found that `rt_metal_create_device` and `rt_metal_present` did not
have one repository-wide ABI. The canonical owner declares indexed device
creation and boolean presentation, while the GPU-session facade redeclared
zero-argument creation and text presentation under the same symbol names. The
Engine2D session also redeclared device creation and compute-pipeline creation
with incompatible signatures. A linker could therefore resolve a valid symbol
whose calling contract belonged to a different consumer.

The two unadmitted pseudo-provider families now use scoped
`rt_gpu_session_metal_*` and `rt_engine2d_metal_session_*` identities. All 14
declarations are explicitly `unsafe(ffi)` and state that their providers are
not admitted. Missing providers now fail symbol resolution rather than
accidentally binding to an incompatible canonical Metal implementation. A
static audit rejects restoration of the colliding declarations and fixes both
pseudo-provider inventories.

The rename changes no successful provider call, branch, allocation, copy, or
GPU data path because no matching provider implementations were found for the
pseudo-provider contracts. It removes an ABI-confusion path rather than adding
a compatibility adapter. Declaration totals remain unchanged; 14 previously
untagged rows are now unsafe-tagged. An authoritative unique-symbol recount is
required after the complete Metal pass because separating formerly colliding
identities intentionally changes symbol cardinality. Exact-artifact signed
admission remains zero.

## Canonical Metal contract and fabricated-stub checkpoint

The canonical Metal owner now has 40 raw declarations, all with adjacent,
operation-specific `@unsafe(... capabilities: [ffi])` contracts. They cover
runtime/device queries, resource handles, borrowed and mutable byte arrays,
shader text, command submission, blocking completion, raw parameter pointers,
batched compute status, and nullable error C strings. The static audit requires
all 40 declarations to retain their tags.

Three additional declarations lived under an explicit `Graphics — Missing
Stubs` heading. Their Rust providers always returned integer zero for sampler
creation, swapchain creation, and presentation, while the Simple facade exposed
dummy resource objects and a boolean presentation result. No consumer existed
outside an async compatibility re-export. The declarations, dummy wrappers,
types, and re-exports are removed rather than converting zero to `false` or
claiming an unsafe stub is a functional API.

The change adds no provider call, dispatch, branch, allocation, copy, or GPU
data movement. It deletes fabricated surface and adds compile-time metadata to
the remaining direct calls. The Metal identity/contract audit and whitespace
check passed; production Simple and optimizer verification remain unavailable.
The refreshed source-only authoritative inventory reports 11,819 `rt_*`
declaration rows / 3,138 `rt_*` symbols, 1,410 unsafe-tagged rows, 10,151
untouched rows, and zero exact-artifact verified-and-signed admissions. The
inventory artifacts are retained at
`/mnt/data/tmp/sffi-inventory.pNuueT/{contracts,symbols}.tsv`.

## Debug canonical-owner consolidation checkpoint

`std.nogc_sync_mut.ffi.debug` duplicated all 43 raw declarations and nearly all
wrapper code from `std.nogc_sync_mut.sffi.debug`. Its differences were naming
comments, one annotation's wording, and the absence of the canonical explicit
export list; no direct consumer of the duplicate namespace was found. The FFI
module is now a two-line compatibility re-export of the canonical SFFI owner.

This removes duplicate declarations and wrapper maintenance without adding a
runtime call, branch, lookup, allocation, copy, or layout change. A static
owner ratchet fixes the canonical inventory at 43 and forbids providers or
wrappers in the compatibility facade; it passed with the whitespace check.

Relative to the refreshed authoritative baseline, estimated `rt_*` declaration
rows decrease from 11,819 to 11,776 while unique symbols remain 3,138.
Unsafe-tagged rows remain 1,410, untouched rows decrease from 10,151 to 10,108,
and exact-artifact verified-and-signed admission remains zero. The 43 canonical
debug declarations remain the next contract-tagging target.

## Debug raw-contract ownership checkpoint

All 43 canonical debug declarations now carry adjacent, operation-specific
`@unsafe(... capabilities: [ffi])` contracts. The metadata distinguishes
debugger global and stack mutation, blocking synchronization, borrowed
pointer/length text inputs, runtime-owned text, OS ptrace process control,
register-map and process-memory ownership, blocking wait status, and owned
DWARF handle/string-array lifetimes. The owner ratchet now requires all 43 raw
declarations to remain explicitly tagged.

This is compile-time ownership metadata only. It changes no syscall, debugger
wait, provider call, allocation, process-memory copy, dictionary/array layout,
or wrapper result. The owner ratchet and whitespace check passed; production
Simple and optimizer verification remain unavailable.

Totals remain an estimated 11,776 `rt_*` declaration rows / 3,138 symbols.
Unsafe-tagged rows increase from 1,410 to 1,453, untouched rows decrease from
10,108 to 10,065, and exact-artifact verified-and-signed admission remains
zero. Raw ptrace and DWARF APIs remain unsafe until their status, absence,
ownership, platform policy, and exact provider evidence are fully admitted.

## CLI canonical-owner and raw-contract checkpoint

`std.nogc_sync_mut.ffi.cli` duplicated all 40 declarations and wrappers from
canonical `std.nogc_sync_mut.sffi.cli`, except that it renamed the generator
surface to `rt_cli_run_ffi_gen`. Repository-wide provider inspection found no
runtime, interpreter, or codegen implementation for that symbol; only
`rt_cli_run_sffi_gen` is implemented and registered. The FFI namespace is now a
canonical re-export with two legacy source-level aliases that call the real
SFFI generator. This eliminates unresolved foreign dispatch while retaining
the legacy function names.

All 40 canonical declarations now carry adjacent, operation-specific
`@unsafe(... capabilities: [ffi])` contracts covering process arguments and
termination, filesystem reads/watches, compiler tagged tuples, command text
and argument arrays, and command exit-status families. The static ratchet
requires all 40 tags, forbids provider declarations in the compatibility
facade, and rejects reintroduction of `rt_cli_run_ffi_gen`; it passed with the
whitespace check.

This removes 40 duplicate foreign declarations. It adds no foreign call,
allocation, array copy, lookup, or command dispatch; only the two cold legacy
generator aliases have one ordinary Simple forwarding call. Estimated totals
are 11,736 `rt_*` declaration rows / 3,137 symbols, 1,493 unsafe-tagged rows,
9,985 untouched rows, and zero exact-artifact verified-and-signed admissions.

## GLFW raw-contract ownership checkpoint

All 40 declarations in the canonical GLFW-shaped hosted adapter now carry
adjacent, operation-specific `@unsafe(... capabilities: [ffi])` contracts. The
metadata identifies borrowed title and clipboard text, window handles and
status returns, runtime-owned event/clipboard text, stateful current-event
snapshots, event/window counts, blocking/global operations, and both ARGB
presentation families. The array form requires dimensions to fit its pixels;
the raw pointer form requires the supplied count to cover the dimensions.

A static ratchet fixes the reviewed inventory at 40 and requires one adjacent
FFI tag per declaration. It passed with the whitespace check. This pass changes
no signature, presentation/event call count, branch, allocation, copy, buffer
layout, event storage, or lookup, so frame and input hot paths are unchanged.
Production Simple and optimizer verification remain unavailable.

Estimated totals remain 11,736 `rt_*` declaration rows / 3,137 symbols.
Unsafe-tagged rows increase from 1,493 to 1,533, untouched rows decrease from
9,985 to 9,945, and exact-artifact verified-and-signed admission remains zero.
The tags do not prove GLFW pointer lifetimes, extent checks, or provider
identity; those require executable contracts and exact signed admission.

## Compiler minimal-runtime raw-contract checkpoint

The compiler's minimal runtime ABI contains 41 declarations, not 40: the
source-only untouched ranking showed 40 because one declaration already had
recognized contract state. All 41 now carry adjacent, operation-specific
`@unsafe(... capabilities: [ffi])` contracts. The metadata distinguishes GC
mutation and allocation, owned runtime-value construction/cloning/release,
borrowed pointer/length strings, discriminants and projections, arithmetic
owned results, tagged-string and exclusive deep-array release, filesystem
pointer/length operations, and environment pointer/length operations.

A static ratchet fixes the inventory at 41 and requires every declaration to
retain its tag. It passed with the whitespace check. This pass changes no ABI
signature, allocation, clone, free, collection traversal, filesystem or
environment call, branch, copy, or runtime-value layout; core hot paths remain
unchanged. Production Simple and optimizer verification remain unavailable.

Estimated totals remain 11,736 `rt_*` declaration rows / 3,137 symbols.
Unsafe-tagged rows increase from 1,533 to 1,573, untouched rows decrease from
9,945 to 9,905, and exact-artifact verified-and-signed admission remains zero.
The raw string out-length and pointer ownership contracts still require typed
ABI validation before this module can be called safe.

## Audio raw-contract ownership checkpoint

The canonical audio owner contains 39 declarations; one pitch contract was
already tagged, and the remaining 38 now carry adjacent, operation-specific
`@unsafe(... capabilities: [ffi])` metadata. The contracts cover engine,
source, playback, SDL2-device, and capture-session handles; path and backend
text; live/queued/frame/underrun counts; spatial listener/source state; and PCM
array or raw pointer/count inputs. The PCM contracts explicitly require the
array or pointed storage to cover the declared sample/channel/frame extent.

A static ratchet fixes the inventory at 39 and requires every declaration to
remain tagged. It passed with the whitespace check. This pass changes no ABI
signature, playback/queue call count, callback, sample conversion, allocation,
buffer copy, queue query, or audio data layout; latency-sensitive paths remain
unchanged. Production Simple and optimizer verification remain unavailable.

Estimated totals remain 11,736 `rt_*` declaration rows / 3,137 symbols.
Unsafe-tagged rows increase from 1,573 to 1,611, untouched rows decrease from
9,905 to 9,867, and exact-artifact verified-and-signed admission remains zero.
Executable extent validation and exact provider evidence remain required before
raw PCM or generation-handle operations can be treated as verified-safe.

## Bootstrap allocation raw-contract checkpoint

All 37 declarations in the bootstrap standard library allocation module now
carry adjacent, operation-specific `@unsafe(... capabilities: [ffi])` metadata.
The contracts distinguish owned heap pointers and reallocation failure,
runtime array/dictionary handles and mutation, owned result handles, untyped
pop/get/lookup absence sentinels, dynamic `Any` dictionary keys, runtime text
ownership, string-derived array handles, and in-place collection operations.

A static ratchet fixes the inventory at 37 and requires every declaration to
retain its tag. It passed with the whitespace check. This pass changes no ABI
signature, allocation/reallocation/free call, collection traversal, clone,
string transformation, branch, copy, handle layout, or dispatch. Core memory
and collection hot paths remain unchanged; production Simple and optimizer
verification remain unavailable.

Estimated totals remain 11,736 `rt_*` declaration rows / 3,137 symbols.
Unsafe-tagged rows increase from 1,611 to 1,648, untouched rows decrease from
9,867 to 9,830, and exact-artifact verified-and-signed admission remains zero.
The dynamic-key ABI and untyped collection absence/error returns must be
replaced by canonical typed contracts before safe publication.

## Simple-core process/time/panic raw-contract checkpoint

All 36 raw libc/runtime declarations in `simple-core` process support now carry
adjacent, operation-specific `@unsafe(... capabilities: [ffi])` metadata. The
contracts cover process termination, fork/exec/wait and process groups, signal
handlers and signal-set pointers, time output structures, heap allocation,
unchecked pointer/offset loads and stores, NUL-terminated string pointers,
tagged string/array/tuple values, and owned argument-array value transfer.

A static ratchet fixes the inventory at 36 and requires every declaration to
retain its tag. It passed with the whitespace check. This pass changes no ABI
signature, fork/exec/signal/time call, allocation/free, pointer access,
argument construction, collection operation, branch, copy, or layout.
Production Simple and optimizer verification remain unavailable.

Estimated totals remain 11,736 `rt_*` declaration rows / 3,137 symbols.
Unsafe-tagged rows increase from 1,648 to 1,684, untouched rows decrease from
9,830 to 9,794, and exact-artifact verified-and-signed admission remains zero.
Signal-handler validity, pointer extents, post-fork restrictions, and exact
libc/runtime identity still require executable policy and admission evidence.

## Simple-core string/stdio raw-contract checkpoint

All 35 raw declarations in `simple-core` string and string-backed stdio now
carry adjacent, operation-specific `@unsafe(... capabilities: [ffi])` metadata.
The contracts cover heap ownership, memory copy/compare extents, integer/float
parsing with end-pointer outputs, NUL-terminated strings, file-descriptor
pointer/count I/O, unchecked pointer/offset access, tagged array/dictionary
handles, borrowed array item pointers, owned value construction, and enum
identity/discriminant/borrowed-payload projections.

A static ratchet fixes the inventory at 35 and requires every declaration to
retain its tag. It passed with the whitespace check. This pass changes no ABI
signature, registry scan, allocation/reallocation/free, parsing operation,
syscall, memory copy, collection traversal, branch, value layout, or dispatch.
The compact string registry and all string hot paths remain unchanged;
production Simple and optimizer verification remain unavailable.

Estimated totals remain 11,736 `rt_*` declaration rows / 3,137 symbols.
Unsafe-tagged rows increase from 1,684 to 1,719, untouched rows decrease from
9,794 to 9,759, and exact-artifact verified-and-signed admission remains zero.
Pointer extents, parsing end-pointer validity, and borrowed payload lifetimes
still require executable validation and exact provider admission.

## Simple-core filesystem raw-contract checkpoint

All 34 raw declarations in `simple-core` filesystem support now carry adjacent,
operation-specific `@unsafe(... capabilities: [ffi])` metadata. The contracts
cover heap ownership, NUL-terminated paths and modes, FILE/DIR/descriptor
handles, stdio element extents, descriptor buffer extents, mmap address/length
lifetime, borrowed `dirent` pointers, rename/remove paths, tagged string/array
results, value transfer, and unchecked pointer/offset access.

A static ratchet fixes the inventory at 34 and requires every declaration to
retain its tag. It passed with the whitespace check. This pass changes no ABI
signature, path copy/normalization, allocation/free, file or directory syscall,
read/write count, mmap operation, directory scan, buffer copy, branch, or
layout. Production Simple and optimizer verification remain unavailable.

Estimated totals remain 11,736 `rt_*` declaration rows / 3,137 symbols.
Unsafe-tagged rows increase from 1,719 to 1,753, untouched rows decrease from
9,759 to 9,725, and exact-artifact verified-and-signed admission remains zero.
Partial-I/O, mmap failure sentinels, directory-entry lifetime, and exact libc
identity still require executable validation and signed admission.

## Hosted Winit canonical-owner checkpoint

`os.hosted.hosted_entry` locally redeclared 30 Winit functions. Six were absent
from the canonical owner, while overlapping declarations disagreed on ABI:
event/window/loop release returned `bool` canonically but was declared void in
hosted entry, and fullscreen read/write returned `bool` canonically but was
declared `i64` locally. The six missing scancode, shifted-key, wheel-x, native
surface-kind, native-display, and native-window contracts are now canonical,
and hosted entry imports all 30 symbols directly from that owner.

Hosted fullscreen logic now uses the canonical boolean values rather than
numeric comparisons/conversions. This fixes the declared ABI instead of
representing booleans as numbers. The four irreducible wall-clock, monotonic
clock, nullable environment, and argument-array declarations remain local and
are explicitly `unsafe(ffi)`.

The owner audit requires 35 tagged canonical Winit declarations, forbids local
Winit externs, fixes the four local declarations, and rejects numeric boolean
adaptation. It passed with the whitespace check. No wrapper, event poll,
provider call, branch, allocation, buffer copy, or render/event data-layout
change was added. Estimated totals decrease from 11,736 to 11,712 declaration
rows while symbols remain 3,137; unsafe-tagged rows become 1,762, untouched
rows become 9,692, and exact signed admission remains zero.

## TLS 1.3 context raw-contract checkpoint

All 48 declarations in the TLS 1.3 context I/O module now carry adjacent,
operation-specific `@unsafe(... capabilities: [ffi])` metadata. The contracts
cover network and IPC transport, blocking sleep, record receive/parsing,
byte-array indexing/allocation, ClientHello and X25519, HKDF and secret caches,
SHA-256/transcript/HMAC derivation, encrypted handshake extraction, record
metadata, certificate/key/signature parsing, and inner-plaintext decoding.

The metadata explicitly identifies ambiguous empty-array failures, untyped
parser/status/discriminant sentinels, cache-take ownership, and the numeric
byte-equality result. It does not treat empty bytes or zero as verified success.
A static ratchet fixes the inventory at 48 and requires every declaration to
retain its tag; it passed with the whitespace check.

This pass changes no ABI signature, network/IPC call, hash, HMAC, HKDF, key
agreement, record parse, allocation, byte-array copy, cache lookup, branch, or
cryptographic data layout. Production Simple and optimizer verification remain
unavailable. Estimated totals remain 11,712 declaration rows / 3,137 symbols;
unsafe-tagged rows increase from 1,762 to 1,810, untouched rows decrease from
9,692 to 9,644, and exact signed admission remains zero.

## Authoritative inventory refresh after TLS context

The refreshed source-only inventory reports 11,713 `rt_*` declaration rows and
3,137 `rt_*` symbols. Of those rows, 1,737 are unsafe-tagged, 9,720 remain
untouched, and zero are exact-artifact verified-and-signed admissions. The
broader all-extern ledger contains 13,475 rows / 3,936 symbols, with 1,922
unsafe-tagged and 11,060 untouched. These authoritative classifications replace
the intervening arithmetic estimates, which cannot account for every
non-`rt_*`, predeclared-contract, or shared-symbol classification.

The inventory artifacts are retained at
`/mnt/data/tmp/sffi-inventory.F4tIYb/{contracts,symbols}.tsv`. The largest owned
production untouched file is now bootstrap `infra/file_io.spl` with 33 rows;
tests and duplicated test layouts remain separately visible but do not outrank
production boundary ownership work.

## Bootstrap file-I/O raw-contract checkpoint

The bootstrap `infra/file_io.spl` owner contains 35 declarations; two optional
read returns already had recognized contract state, and all declarations now
carry adjacent, operation-specific `@unsafe(... capabilities: [ffi])` metadata.
The contracts cover path metadata, optional text-line/byte reads, text and byte
writes, atomic/append operations, copy/move/rename/remove, canonical paths,
directory list/glob/walk and recursive mutation, path decomposition/joining,
current-directory state, and file-descriptor open/size/close.

The metadata identifies ambiguous non-optional empty text/list results rather
than treating them as proven success. A static ratchet fixes the inventory at
35 and requires every declaration to retain its tag; it passed with the
whitespace check. No preflight call, filesystem operation, recursive scan,
allocation, buffer copy, path normalization, branch, or descriptor operation
was added. Production Simple and optimizer verification remain unavailable.

Relative to the refreshed authoritative baseline, declaration rows and symbols
remain 11,713 / 3,137. Unsafe-tagged rows increase from 1,737 to 1,770,
untouched rows decrease from 9,720 to 9,687, and exact signed admission remains
zero. Non-optional empty results still require typed `Result` migration.

## Runtime canonical-owner consolidation checkpoint

`std.nogc_sync_mut.ffi.runtime` duplicated the canonical
`std.nogc_sync_mut.sffi.runtime` module's 32 raw declarations and wrappers; the
only differences were the heading comments. No direct consumer of the duplicate
namespace was found. The FFI module is now a two-line compatibility re-export
of the canonical SFFI owner.

This removes duplicate boundary declarations and wrapper maintenance without a
runtime call, branch, allocation, GC operation, value clone/free, copy, lookup,
or layout change. A static owner ratchet fixes the canonical inventory at 32
and forbids declarations or wrappers in the compatibility facade; it passed
with the whitespace check.

Estimated declaration rows decrease from 11,713 to 11,681 while symbols remain
3,137. Unsafe-tagged rows remain 1,770, untouched rows decrease from 9,687 to
9,655, and exact-artifact verified-and-signed admission remains zero. The 32
canonical runtime declarations remain the next contract-tagging target.

## Runtime-value raw-contract ownership checkpoint

All 32 declarations in the canonical runtime SFFI owner now carry adjacent,
operation-specific `@unsafe(... capabilities: [ffi])` metadata. The contracts
cover GC initialization/collection/allocation, owned scalar/string/array/dict
value construction, borrowed string pointer/length input, type discriminants
and projections, raw string pointer/out-length projection, clone/free ownership,
arithmetic owned results, comparisons, and value output.

The owner ratchet now requires all 32 canonical declarations to retain their
tags in addition to forbidding duplicate providers in the compatibility
facade. It passed with the whitespace check. This pass changes no ABI signature,
GC operation, allocation, clone/free, arithmetic, comparison, output, branch,
copy, value layout, or dispatch. Production Simple and optimizer verification
remain unavailable.

Estimated totals remain 11,681 declaration rows / 3,137 symbols.
Unsafe-tagged rows increase from 1,770 to 1,802, untouched rows decrease from
9,655 to 9,623, and exact-artifact verified-and-signed admission remains zero.
Allocation failures, projection validity, raw string out-length, and owned
result lifetimes still require executable validation and signed admission.

## System environment/process/time raw-contract checkpoint

All 39 declarations in the canonical system owner now carry adjacent,
operation-specific `@unsafe(... capabilities: [ffi])` metadata. Eight process
contracts were already tagged, and nullable environment lookup already had
recognized contract state; the pass closes the remaining 30 untouched rows.
The contracts cover home/hostname/UUID text, optional environment lookup and
mutation/snapshots, process arguments and IDs, captured execution/spawn/wait/
kill, shell commands, host capability values, wall/monotonic/local time,
timestamp formatting/parsing/differences, and blocking sleep.

A static ratchet fixes the inventory at 39 and requires every declaration to
retain its tag. It passed with the whitespace check. This pass changes no ABI
signature, environment lookup, process/shell operation, capture allocation,
clock query, timestamp parse/format, sleep, branch, copy, or dispatch.
Production Simple and optimizer verification remain unavailable.

Estimated totals remain 11,681 declaration rows / 3,137 symbols.
Unsafe-tagged rows increase from 1,802 to 1,832, untouched rows decrease from
9,623 to 9,593, and exact-artifact verified-and-signed admission remains zero.
Ambiguous empty text and timestamp/host discriminant sentinels still require
typed results and exact provider admission.

## Canonical I/O raw-contract checkpoint

All 34 declarations in the canonical I/O owner now carry adjacent,
operation-specific `@unsafe(... capabilities: [ffi])` metadata. Four nullable
line/mmap/lock contracts already had recognized state; this pass closes the
remaining 30 untouched rows. The contracts cover file metadata, text/byte
reads and writes, atomic/append/copy/move/delete, legacy and SHA-256 hashes,
file locks, mmap text/bytes, directory list/walk/recursive search/mutation, and
path joining/normalization/decomposition.

The metadata identifies ambiguous non-optional empty text/array/hash results
instead of calling them verified success. A static ratchet fixes the inventory
at 34 and requires every declaration to retain its tag; it passed with the
whitespace check. This pass adds no existence check, filesystem operation,
hash pass, lock attempt, mmap operation, recursive scan, path transformation,
allocation, buffer copy, branch, or dispatch. Production Simple and optimizer
verification remain unavailable.

Estimated totals remain 11,681 declaration rows / 3,137 symbols.
Unsafe-tagged rows increase from 1,832 to 1,862, untouched rows decrease from
9,593 to 9,563, and exact-artifact verified-and-signed admission remains zero.
Ambiguous non-optional empty results and lock/mmap sentinels still require typed
contracts and exact provider admission.

## Canonical AST raw-contract checkpoint

The two no-GC sync AST library modules previously carried the same 29 raw
declarations and wrappers. `std.nogc_sync_mut.sffi.ast` is now the sole owner;
the legacy `std.nogc_sync_mut.ffi.ast` module is a zero-cost re-export facade.
All 29 canonical declarations have adjacent, operation-specific
`@unsafe(... capabilities: [ffi])` metadata covering opaque expression,
argument, and node handles; unchecked indexed child access; runtime-owned text;
release operations; and process-global registry invalidation.

The owner ratchet fixes the inventory at 29, requires every canonical
declaration to retain its tag, and rejects foreign declarations in the legacy
facade. This pass changes no ABI signature, registry lookup, AST traversal,
allocation, string copy, release call, branch, or dispatch. The application
interpreter's separate 28-declaration raw facade remains untouched pending an
ownership/import migration. Production Simple and optimizer verification remain
unavailable.

Estimated totals decrease from 11,681 to 11,652 declaration rows while symbols
remain 3,137. Unsafe-tagged rows increase from 1,862 to 1,891, untouched rows
remain 9,563, and exact-artifact verified-and-signed admission remains zero.

The application interpreter's 29 raw declarations are now also explicitly
tagged while its raw-name relative-import API remains intact. The shared AST
ratchet covers both surfaces. No ABI, boolean representation, registry access,
AST traversal, allocation, copy, release, branch, or dispatch changed.
Estimated unsafe-tagged rows increase from 1,891 to 1,920 and untouched rows
decrease from 9,563 to 9,534; signed exact-artifact admission remains zero.

## SQLite legacy raw-contract checkpoint

All 27 `rt_sqlite_*` declarations in each of the canonical no-GC library,
application SFFI, and application FFI surfaces now carry adjacent
operation-specific `unsafe(ffi)` metadata. They remain deliberately unverified:
the native C provider returns nullable tagged handles and integer sentinels,
while the Rust interpreter fabricates zero or empty text for several invalid
handles. In particular, query stepping conflates done with failure; scalar zero
can be a valid value or failure; and column text can represent SQL NULL,
invalid access, or an empty value.

Fixing this requires one status/out v2 contract introduced atomically across C,
Rust interpreter dispatch, and Simple wrappers. A one-lane return change would
create cross-engine ABI divergence. This annotation pass adds no query,
statement step, column read, string conversion, allocation, copy, branch,
lookup, or dispatch. A static ratchet fixes all three inventories at 27 and
keeps the principal ambiguities explicit. The Simple edits are metadata-only,
so optimizer output would not measure a runtime transformation; native runtime
behavior is covered separately below.

Estimated declaration totals remain 11,652 / 3,137 symbols. Unsafe-tagged rows
increase from 1,920 to 2,001, untouched rows decrease from 9,534 to 9,453, and
exact-artifact verified-and-signed admission remains zero.

## Bootstrap synchronization ABI checkpoint

The bootstrap synchronization module's declarations did not match the Rust
runtime: mutex and RwLock constructors omitted their initial `RuntimeValue`,
mutex unlock omitted the replacement value, Once declared an integer return
where the provider returns void/bool, TLS treated `RuntimeValue` as `i64`, and
the wrapper called provider RwLock unlock shims that are explicit no-ops.

The 26 remaining declarations now match those provider shapes and carry
adjacent `unsafe(ffi)` metadata. Mutex callbacks use the value returned while
the provider lock is held and return the retained/updated value on unlock.
RwLock wrappers consume provider snapshots and use `rt_rwlock_set` for updates
instead of pretending a no-op unlock preserves a guard. TLS stores/loads `Any`
directly. `Once.call` invokes its initializer locally rather than passing it to
the provider's non-executing callback stub and silently marking it done.

This does not make the module verified: the RwLock provider drops its guard
before the Simple callback, CondVar wait/timeout are stubs, and local Once state
is not an atomic cross-thread once-cell. Those contracts remain explicitly
unsafe pending a real guard/token design. The changes add no steady-state
allocation, registry lookup, lock, sleep, spin, copy, or generic dispatch; they
remove two no-op calls and one non-executing callback-provider call.

A static ABI/contract ratchet fixes these signatures and forbids restoration of
the no-op unlock surface. Estimated declarations decrease from 11,652 to 11,651
while symbols remain 3,137. Unsafe-tagged rows increase from 2,128 to 2,154,
untouched rows decrease from 9,326 to 9,302, and exact-artifact signed admission
remains zero.

## Simple-core array raw-contract checkpoint

All 24 allocator, memory, archive-level array, registry, and runtime-array
externs in `core_array_ops.spl` now carry adjacent `unsafe(ffi)` metadata, with
`raw_ptr` capability where raw allocation/header/item addresses cross the
boundary. This includes extent-sensitive loads, stores, and `memcpy`, registry
publication/invalidation, and allocation/status sentinels.

One concrete leak is fixed: if the u64 array header allocation succeeds but its
item allocation fails, the header is now freed before returning failure. A
constant-time upper bound prevents `capacity * 8` overflow, and concatenation
rejects signed length overflow before allocating. These add only failure-path
cleanup and two O(1) guards—no traversal, copy, allocation, registry lookup, or
dispatch. A static ratchet fixes the inventory and cleanup/overflow invariants.
The focused `bin/simple check` completed, but that command identified its binary
as the Rust bootstrap seed; it is recorded only as limited syntax evidence, not
production verification. The Pure Simple optimizer was therefore not replaced
with the seed and remains unavailable for this checkpoint.

Estimated declaration totals remain 11,652 / 3,137 symbols. Unsafe-tagged rows
increase from 2,104 to 2,128, untouched rows decrease from 9,350 to 9,326, and
exact-artifact verified-and-signed admission remains zero.

## FTP/FTPS unbacked-boundary checkpoint

The canonical FTP owner has 25 raw declarations and no C or Rust provider or
interpreter registration in the current tree. Application and GC variants are
already compile-time re-export facades. The LLM Caret storage selector detects
this state and rejects FTP before invoking the boundary instead of accepting a
fabricated handle.

All 25 declarations now carry adjacent operation-specific `unsafe(ffi)`
metadata covering connection ownership, credentials, TLS policy, remote/local
paths, transfers, ambiguous empty text, negative size failure, transfer modes,
and keep-alive state. A static ratchet requires those tags, rejects appearance
of an unreviewed runtime/interpreter provider, and preserves the storage
fail-closed guard. This metadata adds no network/file operation, allocation,
copy, lookup, lock, branch, or dispatch.

Estimated declaration totals remain 11,652 / 3,137 symbols. Unsafe-tagged rows
increase from 2,079 to 2,104, untouched rows decrease from 9,375 to 9,350, and
exact-artifact verified-and-signed admission remains zero.

The native C provider now rejects non-heap scalar values before pointer
untagging on every connection/statement operation, and `close(nil)` no longer
fabricates success. This is an O(1) bit-tag branch with no registry or
allocation. It cannot distinguish a stale or wrong-kind heap object, so the
boundary remains unsafe pending generation-checked typed handles. Transaction
begin/commit/rollback now execute static C literals directly instead of
allocating and copying a temporary runtime string on every call. Strict C11
`-Wall -Wextra -Werror` syntax lint and Clang static analysis completed without
diagnostics; these checks do not constitute artifact signing or formal proof.

The existing ACID probe then passed all eight focused transaction stages across
memory and file databases, including non-vacuous inserts and rollback recovery.
Its later native enterprise-store compilation failed because 14 closure
functions still require the interpreter. That blocker is recorded in
`doc/08_tracking/bug/sqlite_acid_native_store_closure_blocked_2026-08-25.md`;
the overall gate is therefore FAIL, not verified, and was not rerun.

## HTTP and WebSocket legacy raw-contract checkpoint

All 26 HTTP/WebSocket declarations in each of the no-GC library, application
SFFI, and application FFI facades now carry adjacent operation-specific
`unsafe(ffi)` metadata. The contracts cover runtime-owned response tuples,
transport-failure status, generation-encoded client handles, raw server and
WebSocket handles, header arrays, filesystem download/upload paths, and the
ambiguous empty-text WebSocket receive result.

This is metadata only: it adds no DNS query, connection, request, response read,
file operation, allocation, copy, lock, handle lookup, branch, or dispatch, and
preserves native boolean ABIs. The existing provider surface remains incomplete
across lanes and is neither signed nor semantically verified. A static ratchet
fixes each facade at 26 declarations.

Estimated declaration totals remain 11,652 / 3,137 symbols. Unsafe-tagged rows
increase from 2,001 to 2,079, untouched rows decrease from 9,453 to 9,375, and
exact-artifact verified-and-signed admission remains zero.

## Compression and archive raw-contract checkpoint

The no-GC compression facade owns 24 raw gzip, deflate, zip, tar, and tar.gz
declarations. No matching non-vendored C or Rust provider exists in the
repository. All 24 declarations now carry adjacent operation-specific
`unsafe(ffi)` metadata. The reasons preserve the unresolved obligations:
binary bytes are represented as `text`, allocation and output extents are
unknown, empty text conflates valid empty output with failure, integer handles
lack typed ownership/generation, and extraction has no reviewable traversal,
link, overwrite, or expansion-limit policy.

No public API, boolean result, call, branch, allocation, copy, lookup, lock, or
dispatch changed. Adding speculative validation in the safe-looking facade
would not establish provider behavior and could add hot-path work, so the lane
remains explicitly unsafe pending a typed provider contract. A static ratchet
requires all 24 tags and rejects the appearance of an unreviewed provider.

Estimated repository totals are 11,651 declarations / 3,137 symbols.
Unsafe-tagged rows increase from 2,202 to 2,226, untouched rows decrease from
9,254 to 9,230, and exact-artifact verified-and-signed admission remains zero.

## SSH and SFTP raw-contract checkpoint

The canonical no-GC SSH facade owns 23 raw SSH/SFTP declarations; the other
memory/concurrency families and application module are compatibility facades.
No matching transport provider exists in non-vendored runtime C or Rust code.
All 23 declarations now carry adjacent operation-specific `unsafe(ffi)`
metadata, and the stale comment claiming 30 declarations is corrected.

Unresolved obligations include host-key and TLS-equivalent transport policy,
credential/passphrase lifetime, generation-checked session/channel/SFTP
handles, command output bounds, binary channel extents and partial writes,
remote/local path validation, destructive SFTP operations, metadata failure
encoding, and empty-versus-EOF/failure text results. The unrelated in-tree SSH
AES and authentication-test helpers are not providers for this facade.

This is metadata only: it adds no connection, authentication, command, read,
write, transfer, filesystem access, allocation, copy, lookup, lock, branch, or
dispatch. A static ratchet requires all 23 tags and rejects appearance of an
unreviewed provider.

Estimated repository totals remain 11,651 declarations / 3,137 symbols.
Unsafe-tagged rows increase from 2,226 to 2,249, untouched rows decrease from
9,230 to 9,207, and exact-artifact verified-and-signed admission remains zero.

## Process I/O raw-contract checkpoint

The canonical no-GC process owner has 23 declarations and the application
closure owner has 15. The final six and five untagged declarations respectively
now carry `unsafe(ffi)` metadata, and every direct call added by those legacy
declarations is lexically scoped. Browser renderer sandbox spawn/enter still
have no C or Rust provider. File read exists but returns nullable
`RuntimeValue` while both legacy facades declare non-optional `text`. Native
stderr write and flush providers return `i64` status while these facades discard
it through unit declarations; the providers also currently return zero even
when Rust flush reports failure.

The lexical/metadata changes add no syscall, filesystem access, process launch,
poll, allocation, copy, lookup, lock, branch, or generic dispatch. Variable
placement around lexical unsafe regions retains the same single file-size/read
or flush operation per existing loop iteration. A static ratchet fixes both
inventories, requires every tag, rejects an unreviewed browser provider, and
pins the known native signatures until one canonical generated contract
replaces duplicate declarations.

Estimated repository totals remain 11,651 declarations / 3,137 symbols.
Unsafe-tagged rows increase from 2,249 to 2,260, untouched rows decrease from
9,207 to 9,196, and exact-artifact verified-and-signed admission remains zero.

## Shared I/O runtime raw-contract checkpoint

The shared no-GC I/O owner has 37 raw declarations. Its final 18 untagged file,
directory, platform, clock, hash, exit, and shell declarations now carry
operation-specific `unsafe(ffi)` metadata and their direct calls are lexically
scoped. Provider inspection confirmed that raw byte reads, directory lists,
and platform names can return `nil`; those raw declarations are now optional,
while their existing public APIs retain the intended `[]` or `"unknown"`
fallback. This fixes the type contract without an additional provider call,
scan, allocation, or copy.

Remaining unverified semantics include Boolean I/O failure conflation,
recursive-delete policy, empty recursive-walk failure, shell output/status
ambiguity, runtime hash stability, clock failure, and array ownership. The
Rust native `rt_exit` accepts `i32` and never returns, while simple-core accepts
`i64` and returns `i64`; the audit pins this cross-lane ABI conflict pending
generated typed thunks. `rt_shell_exec` remains interpreter-only rather than a
native provider.

All added unsafe regions are compile-time structure. Existing wrappers retain
one provider invocation and their previous algorithms; no filesystem call,
directory traversal, shell launch, allocation, copy, lookup, lock, or generic
dispatch was added.

Estimated repository totals remain 11,651 declarations / 3,137 symbols.
Unsafe-tagged rows increase from 2,260 to 2,278, untouched rows decrease from
9,196 to 9,178, and exact-artifact verified-and-signed admission remains zero.

## Atomic raw-contract and Boolean RMW checkpoint

The canonical no-GC atomic facade had 16 untagged raw declarations and exposed
four safe-looking Boolean read-modify-write methods implemented as separate
load/swap/store calls. `compare_exchange` could swap a value and then overwrite
a concurrent writer while compensating for mismatch; Boolean and/or/not had
the same non-atomic load/store race. The hosted Rust provider now exports four
typed Boolean RMW primitives, and interpreter registration plus native ABI
metadata use the same signatures. The Simple methods each make one direct
foreign call, so compare-exchange drops from as many as three provider calls
to one and Boolean bitwise RMW drops from two calls to one.

All 20 raw atomic declarations are explicitly `unsafe(ffi)` and every call is
lexically scoped. The public Boolean API and true/false types are preserved.
No allocation, copy, retry loop, extra memory ordering fence, registry lookup,
lock, or dispatch was added per call; the corrected operations reduce existing
global-map mutex acquisitions.

Factory wrappers now reject a non-positive allocation handle once, outside the
operation hot path. Manual `free` methods are explicitly unsafe because the
legacy class cannot consume itself or invalidate its private handle; callers
must prevent use-after-free and duplicate release. Ordinary load/store/RMW
methods remain safe only for live objects produced by the checked factories.

This does not make the atomic provider safe. Hosted operations still acquire a
global `Mutex<HashMap>` despite the facade's lock-free claim, use `SeqCst`
regardless of requested ordering, and fabricate zero/false or discard writes
for stale/invalid handles. The simple-core fallback implements only a partial,
single-threaded pointer-backed integer subset. Typed generation-checked direct
slots and ordered thunks remain required before verified admission.

The GC async atomic module was a full duplicate owner with the old multi-call
Boolean implementation and 16 additional untagged declarations. It is now a
zero-runtime-cost compatibility facade over the canonical no-GC sync owner,
matching the existing no-GC async family structure and removing that divergent
unsafe surface.

Estimated repository totals decrease to 11,639 declarations / 3,141 symbols.
Unsafe-tagged rows increase from 2,278 to 2,298, untouched rows decrease from
9,178 to 9,162, and exact-artifact verified-and-signed admission remains zero.

Focused evidence: the direct Boolean RMW truth-table test passed; an eight-
thread contention test proved exactly one successful false-to-true CAS; and
`cargo check -p simple-compiler` completed with four pre-existing unrelated
warnings. The atomic static contract audit passed. These results validate the
Rust provider and registration edits, but they are not signed exact-artifact or
cross-engine production-Simple evidence.

## Fast in-memory database raw-contract checkpoint

The specialized `FastTable` accelerator owns 21 `rt_db_*` declarations backed
by native C and a separate Rust interpreter implementation. It is not the
general embedded-database default; ordinary Simple code should continue to use
PureDatabase. All 21 declarations now carry explicit `unsafe(ffi)` contracts,
all calls are lexically scoped, creation rejects a negative provider handle,
manual destruction is explicitly unsafe, and the nullable managed-text result
is represented as `text?`. Legacy methods remain explicitly unsafe
because zero, empty, default, and `-1` still conflate valid data, absence,
invalid handles, allocation failure, and provider failure.

The C provider no longer casts the three integer batch values to pointers when
a legacy text-mask bit is set; nonzero masks fail closed. Allocation and growth
paths now check overflow/failure and publish replacements only after success.
Text-to-integer updates release retained text storage, and integer primary keys
use `PRId64` so Windows does not truncate them through 32-bit `long`.

The integer hot path remains O(1) average indexed access. It gains no per-call
hash/signature verification, dynamic symbol lookup, lock, generic dispatch, or
copy; the three-value loop loses its text-mask branch. Allocation checks occur
only on existing allocation/growth paths. Native syntax checking and the static
contract audit cover these edits, but they are not proof, cross-engine evidence,
or signed exact-artifact admission. The generationless 64-slot global registry
is unsynchronized and the Rust interpreter contract remains independently
implemented, so this family is not safe or verified.

Estimated repository totals remain 11,639 declarations / 3,141 symbols.
Unsafe-tagged rows increase from 2,298 to 2,319, untouched rows decrease from
9,162 to 9,141, and exact-artifact verified-and-signed admission remains zero.

## oneAPI partial-provider raw-contract checkpoint

The canonical oneAPI facade declares 24 `rt_oneapi_*` operations. Native C,
the seed-only C satellite, and the Rust interpreter dispatcher expose only the
same 14 symbols, all fixed capability-unavailable stubs; device metadata and
selection, shared allocation, both copies, global synchronization, and error
text are unbacked. The Rust dispatcher incorrectly described the partial stub
ABI as the full family and accepts only integer values even where the Simple
surface declares text or byte arrays. This is neither a real oneAPI provider
nor cross-lane typed evidence.

All 24 declarations now carry operation-specific `unsafe(ffi)` metadata, with
`raw_ptr` on allocation, span, module, kernel, and queue operations. Every raw
call is lexically scoped. Invalid pointer/module/queue wrappers now return
`false` instead of fabricating successful release or wait. Host-data allocation
now observes copy failure, releases the allocation on that error path, and
returns an invalid value instead of reporting a populated device allocation.

No successful allocation, copy, compile, lookup, launch, wait, or release path
gains hashing, signature verification, provider discovery, dynamic lookup,
allocation, copying, locking, or generic dispatch. The host-data helper gains
one required status branch and cleanup only when its existing transfer fails.
Exact signed provider admission remains zero, and this family stays unverified
until a real provider, typed generated registry, ownership/generation model,
and cross-lane tests replace the handwritten partial stubs.

Estimated repository totals remain 11,639 declarations / 3,141 symbols.
Unsafe-tagged rows increase from 2,319 to 2,343, untouched rows decrease from
9,141 to 9,117, and exact-artifact verified-and-signed admission remains zero.

## Engine2D CUDA dynamic-contract checkpoint

The Engine2D CUDA facade owns 23 static declarations and an optional dynamic
driver path. All declarations now carry explicit `unsafe(ffi)` metadata, with
`raw_ptr` for contexts, modules, device memory, argument packs, launches, and
pixel spans. Every static call is lexically scoped and the facade class itself
is unsafe because generationless handles and generic dynamic calls cannot
establish its public invariants.

The dynamic path previously called `cuInit` with no flags argument and treated
the status return of `cuDeviceGetCount`, `cuCtxCreate`, and `cuMemAlloc` as the
requested count/context/pointer even though those APIs return data through out
pointers. Availability now uses `cuInit(0)` and confirms a typed device count;
the three out-parameter operations use their typed static thunks until typed
dynamic thunks exist. Dynamic shutdown no longer fabricates success for an API
the lane cannot perform. Six declared shutdown/argument-pack/pixel-helper
symbols remain wholly unbacked and are pinned by the audit.

Pixel helper wrappers reject invalid handles, negative/misaligned byte extents,
and spans shorter than the requested transfer before entering foreign code.
Context, module, kernel, memory, and launch wrappers reject invalid scalar
contracts in constant time. No valid launch or transfer gains another provider
call, allocation, copy, lock, hash, signature operation, lookup, or generic
dispatch; incorrect dynamic out-parameter calls are removed. This family is
still unsafe and unsigned pending typed provider admission and removal or
implementation of the six missing symbols.

Estimated repository totals remain 11,639 declarations / 3,141 symbols.
Unsafe-tagged rows increase from 2,366 to 2,389, untouched rows decrease from
9,094 to 9,071, and exact-artifact verified-and-signed admission remains zero.

## `CudaDynFfi` authority-reduction checkpoint

The second Engine2D CUDA facade declared 21 static hooks. Twelve were unused,
unbacked helpers/aliases, or an ABI-incompatible function-handle declaration
under the canonical module/name `rt_cuda_launch_kernel` symbol. The facade now
retains only nine provider-backed declarations, all explicitly `unsafe(ffi)`
and lexically scoped. The class itself remains unsafe because dynamic symbol
identity, handle generations, ownership, and pointer arguments are unproved.

Static PTX loading, function lookup, and synchronization now use the canonical
`rt_cuda_module_load_data`, `rt_cuda_module_get_function`, and `rt_cuda_sync`
identities. No exact static function-handle launch provider exists, so that
branch fails closed instead of invoking the canonical symbol with shifted
arguments and undefined behavior. Dynamic mode retains its one direct
`cuLaunchKernel` call. Legacy shutdown also returns failure rather than claiming
an operation that the facade cannot perform.

Scalar guards reject invalid device, module, function, allocation, geometry,
and shared-memory inputs before foreign execution. Generic dynamic dispatch is
still prohibited for device count, context creation, and memory allocation
because those CUDA APIs return through out pointers. Valid dynamic launch and
typed static calls gain no allocation, copy, lookup beyond the already selected
symbol, lock, hash, signing work, provider call, or adapter layer.

Estimated repository totals decrease to 11,627 declarations / 3,141 symbols.
Unsafe-tagged rows increase from 2,389 to 2,398, untouched rows decrease from
9,071 to 9,050, and exact-artifact verified-and-signed admission remains zero.

## ROCm I/O raw-contract checkpoint

The ROCm I/O facade's 23 declarations are backed by a real optional Linux C
provider that loads HIP/HIPRTC once and caches typed function pointers. The
Rust interpreter lane is not that provider: it is a fixed unavailable
simulation returning false, zero, `-3`, and empty text. Source presence and
registration therefore do not establish cross-lane semantic verification.

All 23 declarations now carry operation-specific `unsafe(ffi)` metadata, with
`raw_ptr` for memory, module, function, stream, span, and launch operations.
Every raw call is lexically scoped. Device-name and last-error managed-text
returns are nullable at the raw boundary; their existing nonoptional public
APIs fail closed if runtime allocation returns nil rather than fabricating
text. Invalid release/wait no longer reports success.

Allocation rejects non-positive extents. Host/device/device copies validate
known allocation sizes, launch validates positive geometry and shared memory,
and one-dimensional grid rounding avoids overflow and division by zero. A
failed host-data transfer releases its allocation and returns invalid. These
are constant-time checks; successful calls add no provider invocation,
allocation, staging buffer, copy, lookup, lock, hash, signature operation, or
generic dispatch. The provider's existing array-layout staging and per-launch
argument allocations remain a performance/ownership verification obligation,
not a regression introduced here.

Estimated repository totals remain 11,627 declarations / 3,141 symbols.
Unsafe-tagged rows increase from 2,398 to 2,421, untouched rows decrease from
9,050 to 9,027, and exact-artifact verified-and-signed admission remains zero.

## SDL3 I/O raw-contract checkpoint

The SDL3 facade has 22 Simple declarations backed by the optional C provider
and a family-specific Rust interpreter dispatcher. All declarations now carry
operation-specific `unsafe(ffi)` metadata and every raw call is lexically
scoped. Event-text and error-text lifts are nullable at the raw boundary; the
public wrapper returns a backend error or panics with a stable SFFI diagnostic
when the lift fails instead of fabricating empty text.

The interpreter continues to use typed C signatures and rejects null C text.
Its library handle was already cached, but every event accessor still repeated
`dlsym`. A fixed 24-slot atomic symbol cache now resolves each address once,
without a mutex, map, allocation, or per-call ownership copy. The scalar event
path otherwise retains the same provider-call count and constant-space data
flow. Text events retain their existing single managed-text allocation.

This establishes source-level unsafe authority, provider/registry coverage,
null rejection, and a static contract ratchet. It does not authenticate the
SDL3 library or bind it to signed evidence; provider state is also process
global and remains unsafe. Estimated repository totals remain 11,627
declarations / 3,141 symbols. Unsafe-tagged rows increase from 2,421 to 2,443,
untouched rows decrease from 9,027 to 9,005, and exact-artifact
verified-and-signed admission remains zero.

## Shared GPU foreign-text null checkpoint

The Rust interpreter GPU adapter used one shared `c_ptr_to_string` lift for
Metal device/error text and feature-enabled CUDA device/error text. A null
provider pointer was converted to `String::new()`, fabricating valid empty text
where the foreign contract had failed. The lift now returns a typed runtime
error naming the symbol; all four callers propagate it.

The success path retains the same single C-string scan and owned-string
allocation. The only added work is the required null comparison, with no extra
provider call, copy, lookup, lock, hash, signing operation, or dispatch.
`metal-sffi-symbol-identity.shs` passes and pins the non-fabrication rule. The
focused Rust test passed (1 test, zero failures; 3,928 unrelated compiler tests
filtered out).

This fixes one shared lifting defect but does not yet scope the 67 raw Metal
calls in the Simple facade or authenticate the provider. Census and declaration
counts are unchanged; exact-artifact verified-and-signed admission remains
zero.

## SDL2 event-consumer authority checkpoint

The canonical SDL2 facade already tagged its 65 raw declarations, but two
production consumers bypassed its lexical boundary for 29 cached-event reads:
the web UI translator and hosted compositor input backend. Each read is now
inside a minimal `unsafe(ffi)` scope. Safe state updates, event construction,
button interpretation, and key translation remain outside those scopes.

The event-family audit now covers both consumers as well as the provider. It
pins the cached detail accessors as O(1), allocation-free, lock-free, and free
of an extra poll. No event gains a provider call, allocation, ownership copy,
lookup, lock, hash, signature operation, or dispatch layer.

The same source census before and after the edit measured the SDL2 family
moving from 107 explicit / 29 missing authority call sites to 136 explicit /
zero missing. Repository-wide missing authority fell from 18,339 to 18,310;
production missing authority fell from 10,169 to 10,140. Declaration totals
remain 11,627, with 2,443 unsafe-tagged and 9,005 untouched declaration rows.
Exact-artifact verified-and-signed admission remains zero.

## Canonical Metal facade authority checkpoint

The canonical Metal file's 40 declarations were already tagged, but its 67
production raw calls lacked authority. Typed public wrappers now confine FFI
to lexical blocks. The lower `metal_sffi_*` surface remains explicitly unsafe
at function scope because it exposes generationless device, buffer, shader,
pipeline, queue, command, encoder, and pointer-bearing frame contracts.

Invalid release and wait wrappers no longer manufacture success. Allocation
rejects non-positive extents, texture creation rejects non-positive geometry,
and uploads/downloads reject a span larger than the recorded buffer extent.
Quarantine cleanup preserves dependencies unless wait or registry removal
proves terminal ownership, as before.

The authority scopes and scalar guards add no provider invocation, allocation,
copy, lookup, lock, hash, signature operation, or dispatch. Successful GPU
operations keep their existing direct call shape. The source census measured
missing authority decreasing by exactly 67: 18,274 to 18,207 repository-wide
and 10,104 to 10,037 in production (35 new lexical and 32 function-scoped
authorities). Declaration totals remain 11,627, with 2,449 tagged and 8,999
untouched; exact-artifact verified-and-signed admission remains zero.

## TCP byte-write consumer checkpoint

Two duplicate TCP consumers bypassed the canonical facade's authority: SSH
client transport called `rt_io_tcp_write`, and the async driver called
`rt_io_tcp_write_bytes`. Both declarations and calls now use minimal lexical
`unsafe(ffi)` scopes. The SSH adapter rejects invalid descriptors, zero
progress for nonempty input, and provider counts larger than the borrowed
slice before advancing its send cursor.

The native C provider remains a direct descriptor/array validation followed
by one `write(2)` call; the interpreter uses its typed network registration.
No provider call, allocation, copy, lookup, lock, hash, signature operation,
or dispatch layer was added. The existing SSH suffix slicing remains a known
copying cost and is not claimed verified by this authority change.

The source census measured missing authority decreasing from 18,276 to 18,274
repository-wide and from 10,106 to 10,104 in production. `rt_io` now has 315
explicit and 25 missing call sites. Declaration totals remain 11,627;
unsafe-tagged declarations increase from 2,447 to 2,449 and untouched
declarations decrease from 9,001 to 8,999. Exact-artifact
verified-and-signed admission remains zero.

## Synchronous file I/O raw-contract checkpoint

The canonical `FileHandle`/`File` facade has 16 explicitly unsafe declarations
backed by both typed interpreter registrations and a native Rust C ABI. Its 20
production raw calls were outside lexical authority; each is now scoped to the
exact provider operation. Negative read extents are rejected before crossing
the boundary.

Provider review found that both write functions passed `(null, 0)` to Rust's
`slice::from_raw_parts`, which is undefined behavior even for an empty slice.
Zero-length writes now use `&[]`; nonempty writes validate both pointer and
target `usize` extent. Bounded reads replace infallible `vec![0; size]` with
checked conversion and fallible exact reservation, returning the existing nil
failure sentinel rather than aborting on capacity failure.

Valid reads retain one buffer allocation and one read; valid writes retain one
write call and no new allocation or copy. No lookup, lock, hash, signing work,
or generic dispatch was added. The Rust provider still accepts generationless
raw file descriptors, `read_all` remains caller-unbounded, and boolean
exists/delete results cannot distinguish false from provider failure, so this
family remains unsafe and unsigned.

The source census measured repository-wide missing authority decreasing from
18,310 to 18,290 and production missing authority from 10,140 to 10,120. The
broader `rt_io` family now has 306 explicit and 34 missing call sites.
Declaration totals remain 11,627, with 2,443 unsafe-tagged and 9,005 untouched
rows; exact-artifact verified-and-signed admission remains zero.

Focused Rust provider verification passed: 81 `file_io`-filtered tests, zero
failures (1.01 seconds; 1,146 unrelated tests filtered out).

## Aspect-pack I/O authority and overflow checkpoint

The compiler aspect-pack loader had four tagged file calls but also four
untagged mmap, unmap, raw-pointer-read, and file-size declarations. All eight
declarations and their 14 production call sites now carry minimal lexical FFI
authority; pointer operations additionally require `raw_ptr`.

Both mapping and positioned-read EOF checks previously formed
`offset + length` on attacker-controlled geometry before comparing it with the
file size. They now use subtraction after validating positive bounded length,
so signed overflow cannot turn an out-of-file range into an admitted one. The
existing 64 MiB materialization cap, aligned mapping arithmetic, one
open/map/close sequence, and one open/seek/read/close sequence are unchanged.
The per-byte mapped copy gains only compile-time authority metadata: no extra
call, allocation, copy, branch, lookup, lock, hash, or signing operation.

The source census measured repository-wide missing authority decreasing from
18,290 to 18,276 and production missing authority from 10,120 to 10,106. The
broader `rt_io` family now has 313 explicit and 27 missing call sites.
Declaration totals remain 11,627; unsafe-tagged declarations increase from
2,443 to 2,447 and untouched declarations decrease from 9,005 to 9,001.
Exact-artifact verified-and-signed admission remains zero.

## Engine2D Vulkan raw-facade authority checkpoint

The Engine2D Vulkan owner has 59 already-tagged declarations and 90 production
calls that were previously treated as safe. Its ABI selectors, dual-dispatch
class methods, generationless handle/resource façades, quarantine ownership,
presentation operations, and headless device selection are now explicitly
unsafe at their narrow function boundaries. The checked compute orchestrator
also remains unsafe because scalar validation cannot prove foreign handle
generation, aliasing, or provider identity.

No generic Vulkan driver calls were introduced. Dynamic mode retains exactly
one `vkEnumerateInstanceVersion` loader probe and rejects operational dispatch;
static mode keeps direct typed thunks. Existing region and strided-copy bounds
remain capped and overflow-safe. Authority metadata adds no provider call,
allocation, copy, lookup, lock, hash, signature work, branch, or dispatch.

The source census measured missing authority decreasing by exactly 90: 18,207
to 18,117 repository-wide and 10,037 to 9,947 in production. All 90 became
function-scoped authorities. Declaration totals remain 11,627, with 2,449
tagged and 8,999 untouched; exact-artifact verified-and-signed admission
remains zero.

## Engine2D Vulkan alias-facade authority checkpoint

The sibling `ffi_vulkan.spl` module is an alias facade over the canonical
`rt_vulkan_*` ABI rather than a separate provider. Its 48 production calls now
carry function-scoped FFI authority across the raw `VulkanDynFfi` methods and
the global `vulkan_ffi_*` compatibility entry points. These APIs remain unsafe
because they expose generationless raw handles and cannot establish provider
identity, object lifetime, or aliasing from their scalar inputs.

Dynamic mode remains resolve-only: it looks up
`vkEnumerateInstanceVersion` but does not invoke an operational generic
dispatcher. Static mode continues to call the existing typed canonical
thunks. The annotations add no provider call, allocation, copy, lookup, lock,
hash, signing work, runtime branch, or dispatch overhead.

The source census measured missing authority decreasing by exactly 48: 18,117
to 18,069 repository-wide and 9,947 to 9,899 in production. All 48 became
function-scoped authorities. The broader `rt_vulkan` family now has 134
explicit and 324 missing call sites. Declaration totals remain 11,627, with
2,449 tagged and 8,999 untouched; exact-artifact verified-and-signed admission
remains zero.

## Lyon graphics capability-gap checkpoint

The Lyon graphics module declares 49 raw `rt_lyon_*` functions, but repository
search and the interpreter's capability-gap registry confirm that no native C
or Rust provider exists in tree. Consequently none of its resource handles,
tuples, arrays, text, or boolean results can be promoted to a verified safe
contract. All 49 production wrappers that cross this boundary are now
explicitly function-unsafe, and the negative capability-gap fixture uses a
narrow lexical FFI scope. Invalid resource cleanup now returns `false` instead
of fabricating successful release.

This is authority metadata plus seven fail-closed constant changes on invalid
inputs. Valid paths retain the same direct call, branches, data layout, and
allocations; no provider call, copy, lookup, lock, hash, signing operation, or
dispatch was added. The existing polygon flattening and stroke-options text
construction are unchanged. The identity-only path-transform workaround is
not made safe by this change and remains behind the unsafe boundary.

The source census measured production missing authority decreasing by exactly
49, from 9,899 to 9,850. Including the negative fixture, repository-wide
missing authority decreases by exactly 50, from 18,069 to 18,019: 49 calls
became function-scoped and one became lexically scoped. The `rt_lyon` family
therefore has 50 explicit and zero missing call sites. The fixture adds one
unsafe-tagged declaration; production declaration counts are unchanged.
Exact-artifact verified-and-signed admission remains zero.

## Rapier2D interpreter-provider checkpoint

Rapier2D has 48 tagged raw declarations and an interpreter implementation, but
no matching native C/Rust artifact provider was found outside the interpreter.
All 48 production raw calls, contained in 41 wrapper functions, now carry
function-scoped FFI authority. Three convenience wrappers that delegate to
those functions also propagate the same authority. The facade remains unsafe
because its integer handles have no provider generation, ownership proof, or
signed ABI identity.

Provider review found that ray casting, every joint operation, and joint
counting returned plausible false/zero values despite being unimplemented.
Missing body getters and missing contact records likewise returned valid-looking
zero tuples. These paths now return typed interpreter runtime errors and retain
the last-error diagnostic. Removing an unknown world returns semantic `false`,
and five invalid facade cleanup paths no longer fabricate `true`.

Successful operations retain their existing `HashMap`/mutex access, algorithms,
and allocations. No lookup, lock, copy, hash, signing operation, or dispatch
was added. Diagnostic formatting and allocation occur only on newly fail-closed
error paths. The existing physics-step body-ID vector and contact computation
were not changed or made more expensive.

The source census measured missing authority decreasing by exactly 48: 18,019
to 17,971 repository-wide and 9,850 to 9,802 in production. All 48 became
function-scoped authorities; the `rt_rapier2d` family now has 48 explicit and
zero missing call sites. Focused Rust verification passed four fail-closed
provider tests with zero failures. Exact-artifact verified-and-signed admission
remains zero.

## GPU physics CUDA solver authority checkpoint

The GPU physics solver privately redeclared 12 `rt_cuda_*` operations without
unsafe metadata and invoked them 55 times across compilation, device-buffer
growth, upload, kernel dispatch, download, and destruction. The declarations
and nine raw-calling methods now carry FFI authority; the single top-level
`solve` method propagates that authority because it orchestrates those raw
methods. Pure-Simple spatial hashing, graph coloring, SoA storage, and PTX
kernel material remain unchanged.

This checkpoint is compile-time authority metadata only. It adds no runtime
branch, call, allocation, copy, lookup, lock, hash, signing operation, or
dispatch, and does not change kernel batching or buffer reuse. Review also
found that transfer, launch, synchronization, unload, and free booleans are
ignored, allocation failure can lose capacity truth, and repeated destruction
does not clear every buffer handle. Those are retained as explicit unsafe
obligations rather than being mislabeled verified; they require a separate
fail-closed state-machine patch with measured hot-path evidence.

Provider identity review then found that seven declared names have no runtime
or interpreter implementation: `rt_cuda_memcpy_h2d`, `rt_cuda_memcpy_d2h`,
`rt_cuda_compile_ptx`, `rt_cuda_get_function`, `rt_cuda_synchronize`,
`rt_cuda_stream_create`, and `rt_cuda_stream_destroy`. The declared
`rt_cuda_launch_kernel` ABI is also incompatible with the canonical runtime:
the solver supplies a function handle plus a Simple array and expects `bool`,
whereas the runtime takes a module, length-tracked function name, raw argument
pointer, and returns an integer status. Boolean cleanup cannot repair this ABI
mismatch. The solver must remain unavailable/unsafe until it is regenerated
against the canonical typed CUDA registry; no generic compatibility dispatcher
or numeric coercion should be introduced.

The source census measured missing authority decreasing by exactly 55: 17,971
to 17,916 repository-wide and 9,802 to 9,747 in production. All 55 became
function-scoped authorities. The broader `rt_cuda` family now has 109 explicit
and 337 missing call sites. Twelve declaration rows moved from untouched to
unsafe-tagged. Exact-artifact verified-and-signed admission remains zero.

## Host Vulkan/lavapipe evidence-provider checkpoint

The host lavapipe counterpart exposes two public functions that mutate the
process-global Vulkan ICD selection and directly drive an unsigned Vulkan
provider. Both entries are now explicitly FFI-unsafe. Their 62 previously
unscoped calls became function-scoped; ten newly added calls are also inside
that authority boundary.

The clear/readback path previously multiplied unchecked dimensions, allocated
an unbounded byte array, indexed the first four bytes even when geometry could
produce fewer, accepted a failed depth-image creation, and leaked every valid
depth image. O(1) preflight checks now require positive dimensions no larger
than 8192 per axis and RGBA8 channels in 0..255, capping readback allocation at
256 MiB without overflow. Depth creation fails closed, and six post-creation
cleanup paths release the depth image. The other four new calls provide the
new depth-failure cleanup and diagnostic.

The render/submit/readback hot sequence, pixel-loop complexity, and existing
allocation/copy count are unchanged. No lookup, lock, hash, signing operation,
generic dispatch, or successful-path allocation was added. Cleanup gains one
required destroy call and removes a device-memory leak.

Because ten contract/cleanup calls were added, production raw-call inventory
increased from 12,803 to 12,813 while missing authority still decreased by
exactly 62: 17,916 to 17,854 repository-wide and 9,747 to 9,685 in production.
All 72 calls in the two provider entries are function-scoped. The broader
`rt_vulkan` family now has 206 explicit and 262 missing call sites.
Exact-artifact verified-and-signed admission remains zero.

## VulkanBackend3D lexical-boundary checkpoint

`VulkanRenderBackend3D` implements the ordinary `RenderBackend3D` trait, so
marking whole methods or the trait unsafe would expand authority and could be
bypassed through trait dispatch. Instead, the 18 methods that actually reach
the canonical Vulkan ABI now contain leading lexical `unsafe(ffi)` blocks. All
64 foreign calls are covered while pure command-recording methods and the
public trait shape remain unchanged.

Boundary review added O(1) preflight guards: frame and texture dimensions must
be positive and at most 8192 per axis, each buffer allocation is capped at
256 MiB, buffer uploads reject invalid handles and negative offsets, and
texture uploads reject invalid handles. These checks occur before provider
calls and prevent unchecked geometry, allocation requests, and raw-handle use.

The command array, batching loops, handle-table layout, framebuffer cache, and
provider call count are unchanged. No allocation, copy, lookup, lock, hash,
signing operation, generic dispatch, or loop was added. The guards add one
constant-time branch only at resource creation/upload boundaries, not inside
the recorded-command drain loop.

The source census measured missing authority decreasing by exactly 64: 17,854
to 17,790 repository-wide and 9,685 to 9,621 in production. All 64 became
lexically scoped. The broader `rt_vulkan` family now has 270 explicit and 198
missing call sites. Exact-artifact verified-and-signed admission remains zero.

## Authoritative RT safety census checkpoint

After the VulkanBackend3D checkpoint, the fail-closed
`rt-safety-census.shs` evidence pipeline and its schema/total consistency
contract passed. Unlike textual estimates, this census joins declaration
source-signature hashes with the contract inventory and admits a row as
verified-and-signed only after all nine evidence inputs and the configured
Ed25519 trust policy verify.

Current exact declaration results are 11,627 rows / 3,139 distinct `rt_*`
symbols. All 11,627 remain classified unsafe. Of those, 2,441 declarations are
unsafe-tagged, 999 have documented contracts, 752 are unsafe-minimized, 10,875
remain unsafe-unminimized, and 8,939 are completely untouched. Evidence-
verified, signature-verified, and verified-and-signed rows are all zero.

Owned implementation definitions span four languages: Simple has 685
definitions / 644 symbols in 64 files; Rust has 2,132 / 2,110 in 173 files; C
has 2,396 / 1,894 in 89 files; and C++ has 219 / 219 in one file. These are
implementation-definition counts, not declarations or proof claims.

The call-authority census now also emits a per-file prioritization table from
the same captured call rows. It does not rescan source: aggregation remains
linear in the already-collected call-site count, and the table reports total,
distinct-symbol, lexical, function-level, and missing counts per owner. This
separates high-density owners from family-wide totals without adding a second
tree traversal.

## No-GC async CUDA facade checkpoint

The no-GC async CUDA API imports the canonical tagged CUDA declarations but
had 51 raw calls without local authority. Thirty-eight functions now use
leading lexical blocks: ordinary CUDA calls receive only `ffi`, while the
seven host-allocation, pointer-access, and bit-bridge methods also receive
`raw_ptr`. Class APIs and the canonical one-call wrapper functions retain
their existing signatures.

This checkpoint is compile-time metadata only. It changes no algorithm,
allocation, copy, provider call, loop, lookup, lock, hash, signing operation,
or dispatch. Review found multiple unchecked element-count products before
`count * 8` allocation/copy geometry; those functions remain unsafe and are
queued for a separate overflow-safe extent patch rather than being described
as verified.

The source census measured missing authority decreasing by exactly 51: 17,790
to 17,739 repository-wide and 9,621 to 9,570 in production. All 51 became
lexically scoped. The per-file table now reports this owner as 51 calls / 35
symbols / zero missing. The broader `rt_cuda` family has 138 explicit and 308
missing call sites. Exact-artifact verified-and-signed admission remains zero.

The queued extent patch now centralizes checked f64 byte and two-dimensional
product geometry. Counts above 33,554,432 f64 elements or 256 MiB are rejected
before multiplication, allocation, pointer offset, or device copy. Concatenate
uses subtraction-before-addition, and contiguous 2D copy hoists checked row
bytes outside its loop. Both constant-time helpers carry `@inline`; successful
operations retain the same allocation count, copy count, and loop complexity.
The unavailable production Simple binary prevents executable optimizer/runtime
evidence in this worktree, so the facade remains unsafe and unverified.
## Synchronous CLI SFFI facade checkpoint

`src/lib/nogc_sync_mut/sffi/cli.spl` contains 50 direct raw calls across
40 symbols.  Every call now has a minimal lexical `unsafe(ffi)` scope; the
public signatures and the existing boolean/status semantics are unchanged.
The facade remains O(1) direct delegation and gained no allocation, copy,
lookup, lock, hash, signature operation, or generic dispatch.  The focused
`nogc-sync-cli-sffi-authority.shs` audit passed and guards both the exact call
inventory and the absence of admission work on the call path.

The authoritative call census changed exactly as expected:

- missing authority: 17,739 -> 17,689
- lexical unsafe: 2,519 -> 2,569
- function unsafe: unchanged at 918

Static provider inspection found that `rt_compile_to_native` and
`rt_compile_to_native_with_opt` are not cross-lane ABI-safe: the Simple and
interpreter contracts return `(bool, text)`, but the standalone Rust runtime
exports `i64` functions that currently return a fabricated zero.  This
checkpoint does not coerce that integer into a tuple or claim the provider is
safe.  The ABI must be regenerated from one authoritative contract and the
zero stubs removed before these functions can be admitted outside their unsafe
boundary.

No production Simple optimizer/runtime measurement was possible because this
worktree has no production self-hosted binary.  The static shape evidence is
therefore useful but not performance verification.  Verified-and-signed SFFI
admission remains 0.

## simple-core environment null-contract checkpoint

`core_env.spl` had nine untagged raw declarations and 22 missing-authority
calls.  All declarations now require `ffi, raw_ptr`, and every operation is
confined to a mandatory-inline owner.

Provider comparison found a semantic mismatch: native C and Rust return the
tagged nil sentinel when an environment key is absent or CWD retrieval fails,
but Pure Simple manufactured an empty string.  Pure Simple now returns tagged
nil for absent/invalid keys, allocation/provider failure, and CWD failure.  A
present environment variable whose value is genuinely empty still reaches
`rt_string_new(result, 0)` and remains valid empty text.  Empty keys and
embedded NUL bytes are rejected; the latter check reuses the existing copy
loop and hoists its byte load.

`simple-core-env-authority.shs` passed, pinning call confinement, owner counts,
native/Rust nil behavior, embedded-NUL rejection, inline policy, and byte
intrinsic lowerings.  Census results:

- raw call sites: 19,711 -> 19,698
- missing authority: 15,641 -> 15,619
- lexical unsafe: 3,151 -> 3,160
- function unsafe: unchanged at 919
- distinct called symbols/caller files: unchanged at 3,260 / 3,088

Valid paths retain one O(n) C-string copy, one provider call, and existing
allocations.  The added NUL comparison is within that loop; no extra scan,
copy, allocation, lookup, lock, hash, signature check, or dispatch is added.
Exact-artifact proof remains absent; verified-and-signed admission remains 0.

## simple-core SHA-256 authority/status checkpoint

`core_sha256.spl` had eleven untagged declarations and 21 missing-authority
calls.  All declarations now state their pointer or scalar/handle capability,
and all used calls are confined to mandatory-inline owners.  Eight
pointer-bearing operations require `ffi, raw_ptr`; close/seek and tagged-array
release use `ffi`.

The file-hash path previously ignored failure when rewinding the descriptor and
ignored final close failure before publishing a digest.  Rewind failure now
closes and returns tagged nil.  Final close failure releases the input buffer
and returns tagged nil.  Signed provider statuses remain signed rather than
being reduced to booleans.

`simple-core-sha256-authority.shs` passed, pinning declarations, owners,
archive providers, pointer-intrinsic lowering, inline policy, and rewind/close
admission checks.  Census results:

- raw call sites: 19,698 -> 19,688
- missing authority: 15,619 -> 15,598
- lexical unsafe: 3,160 -> 3,171
- function unsafe: unchanged at 919
- distinct called symbols/caller files: unchanged at 3,260 / 3,088

Valid hashing retains the exact SHA rounds, reads, buffers, and O(file bytes)
work.  Error paths add only cleanup/status branches.  The pre-existing
whole-file input allocation remains explicitly documented in source as a
streaming ponytail; this change adds no allocation, copy, scan, lookup, lock,
hash pass, signature check, or dispatch.  Exact-artifact proof is still absent,
so verified-and-signed admission remains 0.

## simple-core network authority and status checkpoint

`core_net.spl` had eight untagged declarations and 51 missing-authority calls.
All declarations now state pointer versus descriptor authority, and every used
operation is confined to a mandatory-inline owner.  Allocation, sockaddr,
buffer, and byte-store operations require `ffi, raw_ptr`; socket allocation and
descriptor close require `ffi`.

Review found fabricated success in all three probes: TCP connect status was
discarded, UDP send status was discarded, and the HTTP probe returned zero
after connect/write failure or request allocation failure.  Negative provider
errors now propagate unchanged.  Short UDP sends and HTTP writes return
distinct negative errors, and successful work reports a close failure instead
of silently returning zero.  No error is mapped to a boolean.

`simple-core-net-authority.shs` passed, pinning declarations, exact call/owner
inventories, mandatory-inline policy, byte-store intrinsic lowering, and signed
status checks.  Census results:

- raw call sites: 19,754 -> 19,711
- missing authority: 15,692 -> 15,641
- lexical unsafe: 3,143 -> 3,151
- function unsafe: unchanged at 919
- distinct called symbols/caller files: unchanged at 3,260 / 3,088

Normal paths retain the same syscall, allocation, copy, and loop counts.  Extra
descriptor closes occur only on newly fail-closed paths.  No lookup, lock,
hash, signature check, or generic dispatch was added.  Provider semantics and
artifact proof remain incomplete; verified-and-signed admission remains 0.

## simple-core string parser/I/O authority checkpoint

Raw NUL-terminated parsing (`strtoll`, `strtod`, `strlen`) and descriptor I/O
(`read`, `write`) in `core_string.spl` now declare both `ffi` and `raw_ptr`
authority and are confined to five `@always_inline` capability owners.  The
legacy unregistered-pointer `strlen` fallback remains explicitly unsafe rather
than being mislabeled verified; its provenance cannot be established from an
integer address alone.

The extended memory-authority ratchet passed.  The authoritative census moved
the thirteen retained operations behind five lexical owners:

- raw call sites: 20,427 -> 20,419
- missing authority: 16,503 -> 16,490
- lexical unsafe: 3,005 -> 3,010
- function unsafe: unchanged at 919
- distinct called symbols/caller files: unchanged at 3,260 / 3,088

Mandatory inlining preserves the direct parser/syscall operations and adds no
allocation, copy, scan, lookup, lock, hash, signature verification, or generic
dispatch.  Existing signed length/status returns are preserved rather than
converted to booleans.  Production timing/RSS and exact-artifact evidence are
still unavailable; verified-and-signed admission remains 0.

## simple-core string tagged-handle authority checkpoint

All 19 used tagged-value ABI operations in `core_string.spl` are now confined
to mandatory-inline capability owners.  This covers array allocation,
length/get/push/metadata, dictionary queries, boxed scalar conversion, and
enum construction/projection.  The borrowed `array_items` pointer alone
requires `ffi, raw_ptr`; the other operations retain the narrower `ffi`
capability.  Integer discriminants, signed status values, and handles are not
collapsed to booleans or fabricated defaults.

The extended `simple-core-string-memory-authority.shs` ratchet passed with
exact token-boundary confinement and call-inventory checks.  The authoritative
census (50 recognized rows for 54 source occurrences) changed as follows:

- raw call sites: 20,419 -> 20,388
- missing authority: 16,490 -> 16,440
- lexical unsafe: 3,010 -> 3,029
- function unsafe: unchanged at 919
- distinct called symbols/caller files: unchanged at 3,260 / 3,088

The mandatory-inline owners preserve every existing handle operation and add
no allocation, copy, scan, lookup, lock, hash, signature check, or generic
dispatch.  Production timing/RSS and exact artifact/proof receipts remain
unavailable, so the family is explicitly unsafe rather than verified-and-
signed; repository admission remains 0.

## simple-core array-operations authority checkpoint

All 23 raw operations used by `core_array_ops.spl` now have one
`@always_inline` capability owner each.  The set covers libc allocation/copy,
compiler pointer load/store intrinsics, archive-level array header projections
and mutations, registry publication/removal, index normalization, and runtime
array allocation/push.  The unused `numeric_index` declaration remains tagged
but has no call or unsafe scope.  No file- or public-function-wide unsafe
authority was introduced.

`simple-core-array-ops-authority.shs` passed.  It verifies exact raw-call
confinement, mandatory inlining, both native intrinsic lowerings, and the
archive-level provider definitions.  The authoritative census changed exactly
by the 261 previously missing calls moving behind 23 owners:

- raw call sites: 20,388 -> 20,150
- missing authority: 16,440 -> 16,179
- lexical unsafe: 3,029 -> 3,052
- function unsafe: unchanged at 919
- distinct called symbols/caller files: unchanged at 3,260 / 3,088

Mandatory inlining retains the same pointer operation, allocation, copy, and
handle mutation counts.  No validation scan, new allocation/copy, lookup,
lock, hash, signature check, or generic dispatch was added.  Production
timing/RSS and signed exact-artifact proof remain unavailable, so this file is
authority-bounded but not verified-and-signed; repository admission remains 0.

## simple-core filesystem high-volume authority checkpoint

Six operations account for 122 source-level calls in `core_fs.spl`: heap
release, FILE close, descriptor close, runtime string construction, and byte
loads/stores.  Each now has one `@always_inline` minimal owner.  Pointer-bearing
operations require `ffi, raw_ptr`; integer file-descriptor close retains only
`ffi`.  Signed close status and tagged string handles remain unchanged rather
than being converted to booleans or empty values.

`simple-core-fs-authority.shs` passed, pinning exact raw-call confinement,
mandatory inlining, the source inventory, and both compiler pointer-intrinsic
lowerings.  The authoritative census recognized 120 of the 122 source
occurrences and changed as follows:

- raw call sites: 20,150 -> 20,036
- missing authority: 16,179 -> 16,059
- lexical unsafe: 3,052 -> 3,058
- function unsafe: unchanged at 919
- distinct called symbols/caller files: unchanged at 3,260 / 3,088

The transformation preserves every release, close, allocation-producing
string lift, and byte operation.  Mandatory inlining adds no function
dispatch, allocation, copy, scan, lookup, lock, hash, or signature check.
Production timing/RSS and exact-artifact proof remain unavailable; the file
still has lower-volume unbounded calls and verified-and-signed admission
remains 0.

## simple-core process high-volume authority checkpoint

Six operations account for 75 source occurrences in `core_process.spl`: heap
release, raw i64 load, signal delivery, process termination, microsecond sleep,
and tagged-string construction.  Each now has one `@always_inline` minimal
owner.  Pointer-bearing release/load/string operations require `ffi, raw_ptr`;
PID/status-only operations retain `ffi`.  `kill` and `usleep` keep their signed
status results, and no status is converted to a boolean.

`simple-core-process-authority.shs` passed, pinning raw-call confinement,
mandatory inlining, exact source inventory, and both native load-intrinsic
lowerings.  The authoritative census recognized 69 of the 75 occurrences:

- raw call sites: 19,990 -> 19,927
- missing authority: 15,985 -> 15,916
- lexical unsafe: 3,086 -> 3,092
- function unsafe: unchanged at 919
- distinct called symbols/caller files: unchanged at 3,260 / 3,088

Mandatory inlining preserves every release/load/signal/exit/sleep/string
operation and adds no dispatch, allocation, copy, scan, lookup, lock, hash, or
signature check.  Lower-volume process boundaries and exact-artifact proof
remain outstanding; verified-and-signed admission remains 0.

## simple-core process spawn/memory authority checkpoint

The next ten `core_process.spl` operations now have mandatory-inline owners:
zeroed/raw allocation, i64/byte stores, tuple field transfer, borrowed string
data, PID retrieval, fork, exec, and waitpid.  Allocation, pointer stores,
borrowed data, argv, and wait-status output require `ffi, raw_ptr`; tuple and
PID-only operations retain `ffi`.  Fork PIDs, exec errors, and wait results
remain signed integers rather than booleans.

The extended process authority ratchet passed and now pins load/store intrinsic
lowering in both native backends.  The census recognized 41 of 44 source
occurrences:

- raw call sites: 19,927 -> 19,896
- missing authority: 15,916 -> 15,875
- lexical unsafe: 3,092 -> 3,102
- function unsafe: unchanged at 919
- distinct called symbols/caller files: unchanged at 3,260 / 3,088

Mandatory inlining preserves all allocation, store, tuple, fork/exec/wait, and
PID operation counts.  No new dispatch, allocation, copy, scan, lookup, lock,
hash, or signature check was added.  Remaining low-volume process calls and
artifact verification are outstanding; verified-and-signed admission is 0.

## simple-core process complete authority checkpoint

The remaining 20 process/time ABI operations now have mandatory-inline owners:
abort/time/timeval/clock, byte load, array and argv handles, tuple/integer
construction, string length/stderr, parent PID, signal handler/group/set
operations, sysconf, and C-string length.  Pointer outputs, signal handlers,
and C-string access require `ffi, raw_ptr`; scalar and tagged-handle operations
retain `ffi`.

Together with the prior checkpoints, all 36 used raw operations in
`core_process.spl` are confined: 18 pointer-bearing owners and 18 scalar/handle
owners.  `simple-core-process-authority.shs` passed with exact raw-call and
owner inventories, mandatory-inline policy, and all four pointer-intrinsic
lowerings pinned.

The final pass changed the authoritative census as follows:

- raw call sites: 19,896 -> 19,890
- missing authority: 15,875 -> 15,849
- lexical unsafe: 3,102 -> 3,122
- function unsafe: unchanged at 919
- distinct called symbols/caller files: unchanged at 3,260 / 3,088

Signed clock, PID, signal, process-group, and configuration results remain
unchanged.  Mandatory inlining adds no dispatch, allocation, copy, scan,
lookup, lock, hash, or signature check.  Static authority is complete for this
file, but provider semantics and exact-artifact proof are not; verified-and-
signed admission remains 0.

## simple-core array provider authority checkpoint

`core_array.spl`, the archive-level provider used by split array modules, had
14 untagged raw declarations and 65 missing-authority calls.  Every declaration
now carries an explicit contract/capability annotation.  All 11 used raw
operations are confined to mandatory-inline owners: seven pointer-bearing
libc/compiler operations use `ffi, raw_ptr`, while four tagged-string/value
operations use `ffi`.  Three unused declarations remain tagged and uncalled.

Provider review also found an allocation-failure leak in
`array_new_with_flags`: if item storage allocation failed, the already-owned
array header was abandoned.  The failure path now releases that header before
returning zero.  Valid allocation and array hot paths are unchanged.

`simple-core-array-provider-authority.shs` passed, pinning declarations, exact
raw-call confinement, owner inventories, mandatory-inline policy, all four
memory-intrinsic lowerings, and the leak cleanup.  Census results:

- raw call sites: 19,890 -> 19,836
- missing authority: 15,849 -> 15,784
- lexical unsafe: 3,122 -> 3,133
- function unsafe: unchanged at 919
- distinct called symbols/caller files: unchanged at 3,260 / 3,088

Mandatory inlining adds no hot-path dispatch, allocation, copy, scan, lookup,
lock, hash, or signature check.  One `free` is added only on an allocation
failure that previously leaked.  Provider semantics and exact-artifact proof
remain incomplete; verified-and-signed admission remains 0.

## simple-core array-query authority and load-hoisting checkpoint

`core_array_query.spl` had ten untagged raw declarations and 92 recognized
missing-authority calls.  Every declaration is now contract/capability tagged
and every used operation has a mandatory-inline minimal owner.  Pointer loads,
stores, and borrowed item projection require `ffi, raw_ptr`; array handles,
copy/reverse/push, and string join use `ffi`.

The index-of, last-index-of, and count loops previously loaded the same array
slot twice per iteration for their range-style equality test.  Each now loads
once into a local and reuses it.  This preserves the existing comparison
semantics while halving slot-load traffic in those three O(n) hot loops.

`simple-core-array-query-authority.shs` passed, pinning declarations, owners,
provider definitions, both memory-intrinsic lowerings, inline policy, and the
single-load loop shape.  Census results:

- raw call sites: 19,836 -> 19,754
- missing authority: 15,784 -> 15,692
- lexical unsafe: 3,133 -> 3,143
- function unsafe: unchanged at 919
- distinct called symbols/caller files: unchanged at 3,260 / 3,088

No allocation, copy, scan pass, lookup, lock, hash, signature check, or generic
dispatch was added.  The three loops retain O(n) complexity with fewer loads.
Provider semantics and artifact proof remain incomplete; verified-and-signed
admission remains 0.

## simple-core filesystem open/seek authority checkpoint

The next 40 `core_fs.spl` operations—heap allocation, FILE/path opening,
tagged-string data/length projection, and descriptor seek—now route through
six mandatory-inline minimal owners.  Pointer-bearing allocation, path, FILE,
and borrowed string-data operations require `ffi, raw_ptr`; string length and
integer descriptor seek retain only `ffi`.  Zero/negative provider sentinels
remain signed and are not converted to booleans.

The extended filesystem authority ratchet passed.  The authoritative census
changed exactly as expected:

- raw call sites: 20,036 -> 20,002
- missing authority: 16,059 -> 16,019
- lexical unsafe: 3,058 -> 3,064
- function unsafe: unchanged at 919
- distinct called symbols/caller files: unchanged at 3,260 / 3,088

Mandatory inlining preserves one allocator/open/projection/seek operation at
each original site.  No new allocation, copy, scan, lookup, lock, hash,
signature check, or generic dispatch was added.  Lower-volume filesystem calls
and artifact proof remain outstanding; verified-and-signed admission stays 0.

## simple-core filesystem complete authority checkpoint

The remaining 22 filesystem ABI operations now each have a mandatory-inline
minimal owner: C string length, stdio read/write/error/seek/tell, descriptor
read/write/sync, mmap/unmap, directory create/open/read/close, rename/remove,
tagged array allocation/push, byte-array allocation, and i64 pointer
load/store.  The mid-file `remove` declaration was moved into the canonical
declaration block and tagged `ffi, raw_ptr`.

Together with the prior two checkpoints, all 34 raw operations used by
`core_fs.spl` are confined.  Twenty-seven owners require `raw_ptr`; seven
handle/descriptor-only owners require only `ffi`.  The completed
`simple-core-fs-authority.shs` ratchet passed and pins all four compiler memory
intrinsics plus mandatory-inline policy.

The final filesystem pass changed the authoritative census as follows:

- raw call sites: 20,002 -> 19,990
- missing authority: 16,019 -> 15,985
- lexical unsafe: 3,064 -> 3,086
- function unsafe: unchanged at 919
- distinct called symbols/caller files: unchanged at 3,260 / 3,088

All signed status, byte-count, position, pointer, and tagged-handle results are
preserved.  Mandatory inlining adds no call dispatch, allocation, copy, scan,
lookup, lock, hash, or signature check.  This proves static authority shape,
not provider semantics or artifact identity; verified-and-signed admission
remains 0.

## Pure Simple SSH cipher boundary checkpoint

The general SSH cipher no longer declares or calls `serial_println` or
`rt_bytes_u8_at`; it remains a Pure Simple implementation.  Direct bounds-
checked indexing replaces the foreign byte accessor, and the packet hot path
no longer constructs an incrementally concatenated hexadecimal diagnostic or
prints secret-adjacent frame material.

AES-256-GCM now rejects non-32-byte keys, non-12-byte IVs, oversized or
inconsistent SSH frames, unexpected encryption output lengths, and unexpected
decryption plaintext lengths.  Nonces no longer silently zero-pad a short IV.
The focused `ssh-cipher-pure-boundary.shs` static ratchet passed.

The source change removes exactly two missing-authority raw call sites from
this caller, so the census baseline moves from 20,661 to 20,659 raw calls and
from 16,758 to 16,756 missing-authority calls; lexical and function unsafe
counts remain 2,984 and 919.  The valid path retains O(packet bytes) work and
existing packet buffers.  New checks are O(1), occur before allocation/copy
where possible, and add no hashing, signing, lookup, lock, dispatch, or copy.

This checkpoint is a source/static contract result, not production compiler
verification or signed artifact admission.  Repository-wide verified-and-
signed admission remains 0.

## Pure Simple SSH byte-utility checkpoint

`ssh_transport.spl`, `ssh_packet.spl`, and `ssh_kex_primitives.spl` now use
bounds-preserving Pure Simple indexing instead of `rt_bytes_u8_at`.
`ssh_identification.spl` now appends its already-masked byte directly instead
of calling `rt_push_byte`.  These modules consequently have no raw byte-
access/push declarations or calls; the focused
`ssh-pure-byte-boundary.shs` ratchet passed.

The authoritative census changed exactly by the four removed calls:

- raw call sites: 20,659 -> 20,655
- distinct called symbols: 3,261 -> 3,260
- caller files: 3,092 -> 3,088
- missing authority: 16,756 -> 16,752
- lexical unsafe: unchanged at 2,984
- function unsafe: unchanged at 919

Each replacement retains O(1) byte access and the existing O(n) surrounding
loops.  It removes foreign dispatch and adds no allocation, copy, hash,
signature operation, lookup, lock, or generic dispatch.  This is static source
evidence only; verified-and-signed artifact admission remains 0.

## SSH host-key loader contract checkpoint

The loader's local `rt_file_read_bytes` declaration now matches the
authoritative nullable `[u8]?` provider contract.  A missing or failed read is
lifted to `Result.Err` instead of being coalesced to an empty array and then
misreported as an empty file.  The remaining raw byte-to-text conversion is
centralized in one minimal `unsafe(ffi)` wrapper that rejects nil and rejects
an empty text fabricated from non-empty input.  The focused
`ssh-host-key-sffi-contract.shs` ratchet passed.

The authoritative census reflects two duplicate raw conversion calls removed
and the two retained wrapper calls bounded:

- raw call sites: 20,655 -> 20,653
- missing authority: 16,752 -> 16,748
- lexical unsafe: 2,984 -> 2,986
- function unsafe: unchanged at 919
- distinct called symbols/caller files: unchanged at 3,260 / 3,088

Valid reads and conversions preserve their existing O(file bytes) work and
allocation shape.  Error checks are O(1); no per-call hash, signature check,
lookup, lock, generic dispatch, or additional full-buffer copy was added.
Provider lanes still disagree on malformed byte-to-text behavior and no exact
artifact proof/signature receipt exists, so this module remains unsafe rather
than verified-and-signed; repository admission remains 0.

## SSH PTY raw-pointer checkpoint

The PTY facade retains one native `unsafe_addr_of` declaration and eight raw
address extractions, now covered by five minimal `unsafe(ffi, raw_ptr)` scopes.
The unused `mmio_read8` declaration was removed.  Pipe descriptor and buffer
addresses must be nonzero before use; pipe reads cannot claim more than the
bounded requested extent, and writes cannot claim more than the source array.
Zero-length reads now return immediately instead of entering the pipe wait
path.  The focused `ssh-pty-sffi-contract.shs` ratchet passed and confirmed the
native provider signature.

The authoritative census moved exactly the eight calls into lexical authority:

- raw call sites: unchanged at 20,653
- missing authority: 16,748 -> 16,740
- lexical unsafe: 2,986 -> 2,994
- function unsafe: unchanged at 919
- distinct called symbols/caller files: unchanged at 3,260 / 3,088

All new validation is O(1) around the existing pipe operations.  It adds no
allocation, copy, lookup, lock, hashing, signing, or generic dispatch, and the
zero-length fast path avoids unnecessary blocking.  Pointer lifetime/layout
and exact-artifact evidence remain unproved, so this facade is explicitly
unsafe, not verified-and-signed; repository admission remains 0.

## SSH autostart serial-boundary checkpoint

The x86_64 SSH autostart module's five direct `serial_println` calls now route
through one inline helper containing the only minimal `unsafe(ffi)` scope.
The declaration carries explicit FFI authority, and the focused
`ssh-autostart-sffi-contract.shs` ratchet pins both the C header and native
provider to their void return contract.

The authoritative census reflects four duplicate raw call sites eliminated
and the retained wrapper call bounded:

- raw call sites: 20,653 -> 20,649
- missing authority: 16,740 -> 16,735
- lexical unsafe: 2,994 -> 2,995
- function unsafe: unchanged at 919
- distinct called symbols/caller files: unchanged at 3,260 / 3,088

Inlining preserves one serial dispatch per emitted message.  No additional
formatting, allocation, copy, lookup, lock, hashing, signing, or generic
dispatch is introduced; this is a cold boot path rather than a packet hot
path.  Serial output integrity and exact-artifact evidence remain unproved,
so it remains explicitly unsafe and verified-and-signed admission remains 0.

## simple-core string raw-memory authority checkpoint

Four compiler-owned pointer intrinsics (`spl_load_i64`, `spl_store_i64`,
`spl_load_u8`, and `spl_store_u8`) accounted for 192 source-level accesses in
`core_string.spl`.  They now carry both `ffi` and `raw_ptr` declaration
authority and are called only by four minimal capability-owner functions.
Ordinary string-runtime code calls those owners without acquiring file- or
function-wide unsafe authority.

The owners use `@always_inline`, which the Rust LLVM backend maps to LLVM
`alwaysinline` and the self-hosted MIR policy recognizes as an unconditional
inline marker.  Both Cranelift and LLVM intrinsic lowering tables remain
pinned by `simple-core-string-memory-authority.shs`; the focused ratchet
passed.

The authoritative source census (which reports distinct recognized call rows,
not every same-line source occurrence) changed as follows:

- raw call sites: 20,649 -> 20,470
- missing authority: 16,735 -> 16,552
- lexical unsafe: 2,995 -> 2,999
- function unsafe: unchanged at 919
- distinct called symbols/caller files: unchanged at 3,260 / 3,088

After mandatory inlining the machine-level operation remains the same direct
load/store intrinsic: no per-byte call, allocation, copy, lookup, lock, hash,
signature check, or generic dispatch is added.  Production binary timing/RSS
was not available, so this is static code-shape evidence rather than measured
performance verification.  Pointer provenance and artifact evidence remain
unproved; verified-and-signed admission remains 0.

## simple-core string heap/copy authority checkpoint

The six raw libc heap/copy operations used by `core_string.spl` (`malloc`,
`calloc`, `realloc`, `free`, `memcpy`, and `memcmp`) now declare both `ffi`
and `raw_ptr` authority and are reachable only through six minimal
`@always_inline` capability owners.  Existing allocation-failure, pointer,
length, and object-layout checks remain at their semantic call sites; the
change does not invent a success value or broaden whole runtime functions to
unsafe.

The extended `simple-core-string-memory-authority.shs` ratchet passed and
guards exact raw-call confinement, mandatory inlining, and the existing call
inventory.  The authoritative census changed exactly as expected:

- raw call sites: 20,470 -> 20,427
- missing authority: 16,552 -> 16,503
- lexical unsafe: 2,999 -> 3,005
- function unsafe: unchanged at 919
- distinct called symbols/caller files: unchanged at 3,260 / 3,088

The transformation preserves the exact number and placement of libc
allocations, releases, copies, and comparisons.  Mandatory inlining prevents
wrapper dispatch; no validation scan, allocation, copy, lookup, lock, hash, or
signature operation was added.  Production timing/RSS remains unavailable,
so performance evidence is static.  Pointer provenance, allocator ownership,
and signed exact-artifact receipts are still unproved; verified-and-signed
admission remains 0.

## SSH KEX call-authority and hot-path checkpoint

The SSH session KEX owner no longer dispatches its 113 constant packet-byte
appends through `rt_push_byte`; the retained local spelling is an inline Pure
Simple wrapper over `_append_byte`, so byte sequences and array-growth
semantics are unchanged.  Sixty-nine raw serial diagnostic calls were removed,
including transcript, public-key, signature, and exchange-hash hex formatting.
This removes foreign dispatch and avoids diagnostic text/hex allocations from
the handshake path.

The six remaining actual foreign calls in this owner are now inside minimal
lexical `unsafe(ffi)` scopes: X25519 public/shared operations, two SHA-256 KDF
calls, the exchange hash, and bounded retry sleep.  X25519 and SHA-256 results
must be exactly 32 bytes, the exchange hash must be exactly 32 bytes, derived
key lengths are checked before publication, and the KDF request is capped at
64 bytes.  A short/empty SHA-256 result now fails instead of leaving the KDF
expansion loop unable to make progress.

The focused static boundary ratchet passed.  The authoritative census changed:

- missing authority: 17,145 -> 17,070
- lexical unsafe: 2,954 -> 2,959
- function unsafe: unchanged at 919

The valid path adds fixed-width comparisons only and removes per-byte foreign
dispatch and diagnostic allocation work.  No hashing, signing, discovery,
lookup, lock, generic dispatch, or additional copy was added.  Provider ABI,
ownership, compiler/artifact identity, and proof receipts remain unresolved,
so SSH KEX and the wider SFFI surface are not globally safe, verified, or
signed; exact-artifact verified-and-signed admission remains 0.

## SSH session transport and sleep-ABI checkpoint

The parent SSH session owner replaced 41 fixed identification-byte calls to
the raw `rt_push_byte` provider with the same inline Pure Simple `_append_byte`
compatibility helper used by the KEX owner.  It also removed 81 raw serial
diagnostic calls, including ciphertext, packet, authentication, and version
formatting, and replaced the one runtime byte-slice call with the existing
bounded Pure Simple prefix copier.  This removes 123 raw call sites and avoids
diagnostic formatting/hex allocations on send, receive, and authentication
paths.

Provider inspection found that `rt_thread_sleep` is `void` in both
`runtime_thread.c` and the Rust executor.  The SSH declaration incorrectly
claimed an `i64` result; it now matches the provider and the KEX caller no
longer reads a fabricated return register.  Four bounded sleep calls and two
validated byte-to-text lifts use six minimal lexical `unsafe(ffi)` scopes.
Empty text lifts fail closed, send requires the provider to report the full
byte count, and receive sizes are checked against the facade's existing
16 MiB maximum before the `u64` to `i64` conversion.

The focused static boundary ratchet passed.  The authoritative census changed:

- raw call sites: 20,948 -> 20,825
- missing authority: 17,070 -> 16,941
- lexical unsafe: 2,959 -> 2,965
- function unsafe: unchanged at 919

The valid path removes foreign calls and diagnostic work.  Its added checks
are constant-time scalar comparisons; it adds no allocation, copy, hashing,
signature operation, discovery, lookup, lock, or generic dispatch.  The
network facade and providers still lack exact-artifact ABI/proof/signature
admission, so SSH and the broader SFFI surface remain not globally safe,
verified, or signed; exact-artifact verified-and-signed admission remains 0.

## Boot network facade contract and diagnostic checkpoint

The Pure Simple boot-network facade removed 27 serial diagnostic calls, its raw
runtime byte accessor, and one unreachable duplicate version-text provider
call; bounded Simple indexing now decodes already-sized SSH headers.  Normal
socket and identification reads now call the descriptor-aware provider with
the resolved owner instead of consulting the process-global receive stream.
This removes raw calls and formatting work without adding a lookup, allocation,
or copy.

The facade's `rt_thread_sleep` declaration now matches the C and Rust `void`
providers.  Write wrappers accept only the exact reported byte count (including
the fixed 22-byte SSH banner); reads reject results larger than their requested
extent; version text/bytes and plaintext SSH payloads have protocol bounds; and
foreign descriptors are range-checked before narrowing to `i32`.  A redundant
text conversion implementation and unused foreign declarations were removed.

The focused static contract ratchet passed.  The authoritative census changed:

- raw call sites: 20,825 -> 20,796
- missing authority: unchanged at 16,941
- lexical unsafe: 2,965 -> 2,936
- function unsafe: unchanged at 919

The valid path is cheaper: 29 raw calls disappeared and the new validation is
constant-time scalar/length comparison.  Exact provider ABI identity, artifact
signature verification, ownership evidence, and proof receipts remain absent,
so this facade and the broader SFFI surface are not globally safe, verified, or
signed; exact-artifact verified-and-signed admission remains 0.

## Thread-sleep ABI and authority checkpoint

The owned Simple source and tests contain 40 declarations and 55 calls of
`rt_thread_sleep`.  Both authoritative providers are void: C declares
`void rt_thread_sleep(int64_t)` and Rust exports
`extern "C" fn rt_thread_sleep(i64)` without a result.  The two SSH declarations
that claimed an `i64` return now match that ABI, and no caller reads a fabricated
return register.

Every declaration now carries explicit FFI metadata and every standalone call
is enclosed by the smallest lexical `unsafe(ffi)` scope.  This migration adds
compile-time authority only: it does not add a branch, wrapper dispatch,
allocation, copy, lookup, lock, hash, signature operation, or extra sleep.

The repository-wide ABI/authority ratchet passed.  The authoritative census
changed:

- raw call sites: unchanged at 20,796
- missing authority: 16,941 -> 16,905
- lexical unsafe: 2,936 -> 2,972
- function unsafe: unchanged at 919

The symbol is now consistently declared and explicitly unsafe, but provider
artifact identity and proof/signature receipts remain absent.  Therefore the
thread-sleep boundary and the broader SFFI surface are not globally verified
or signed; exact-artifact verified-and-signed admission remains 0.

## SSH helper Pure Simple boundary checkpoint

The SSH helper owner removed 28 per-byte foreign append calls, two raw slice
calls, one raw byte accessor, and two direct serial calls.  Its 37 parser and
validation diagnostic wrapper calls were also removed, avoiding text
interpolation and serial dispatch on malformed or ordinary handshake traffic.
Unused crypto, sleep, byte, and array extern declarations were deleted.

Byte access is now bounds-checked Simple indexing, ranges use the bounded
Simple slice operation, and the retained `rt_push_byte` spelling is an inline
Pure Simple `_append_byte` helper.  The only remaining foreign operation is a
byte-array-to-text lift in `_read_text_field_fast`; it has one minimal lexical
`unsafe(ffi)` scope and rejects non-empty input becoming empty text.  Length
parsing now uses subtraction-based overflow-safe bounds, and KEXINIT trailing
data is rejected instead of merely logged and accepted.

The focused static boundary ratchet passed.  The authoritative census changed:

- raw call sites: 20,796 -> 20,763
- missing authority: 16,905 -> 16,871
- lexical unsafe: 2,972 -> 2,973
- function unsafe: unchanged at 919

The valid byte-building path removes foreign dispatch and adds only constant-
time bounds checks already required before indexing.  No lookup, lock, hash,
signature operation, generic dispatch, or extra copy was introduced.  The
remaining text provider lacks exact-artifact proof/signature admission, so the
SSH helper family and wider SFFI surface remain not globally verified or
signed; exact-artifact verified-and-signed admission remains 0.

## SSH interactive channel and SCP boundary checkpoint

The SSH channel owner removed 24 raw serial diagnostics, four per-byte append
calls, five whole-array concatenations, two raw slices, and three duplicate
byte-to-text calls.  Raw byte scanning now uses the bounds-checked Pure Simple
SSH helper, while basename and command paths use already-validated Simple
slices.

SCP control records now collect decimal digits in reverse once and append them
directly into the output, followed by one pass over the filename.  This removes
the former temporary one-byte array and prepend-concatenation for every digit,
plus four subsequent whole-array concatenations.  The algorithm remains linear
but performs fewer allocations and copies.

One generated text-lift wrapper rejects non-empty input becoming empty text.
The four x86_64 FAT/MMIO declarations now carry explicit `ffi`/`raw_ptr`
authority and their calls use minimal lexical scopes.  File sizes remain capped
at 4 MiB; the buffer extent cannot overflow its address; stream reads must
report the exact size before MMIO access.  The existing bounded sleep retains
one minimal lexical scope.

The focused static boundary ratchet passed.  The authoritative census changed:

- raw call sites: 20,763 -> 20,725
- distinct called symbols: 3,263 -> 3,261
- missing authority: 16,871 -> 16,828
- lexical unsafe: 2,973 -> 2,978
- function unsafe: unchanged at 919

No hashing, signing, lookup, lock, generic dispatch, or additional data copy
was introduced.  FAT/MMIO ownership and exact provider artifact/proof/signature
evidence remain unresolved, so the channel family and wider SFFI surface are
not globally verified or signed; exact-artifact verified-and-signed admission
remains 0.

## SSH authentication Pure Simple checkpoint

The split SSH service-request/authentication owner no longer declares or calls
the raw serial provider.  Thirteen packet/authentication diagnostic calls were
removed, including full pre-auth packet hex formatting.  The module now has no
foreign declaration or call.

Authentication semantics are unchanged: booleans remain booleans, malformed
text fields fail through the hardened helper `Result`, password fields are not
copied to immutable text, request attempts remain bounded, and equal-length
credential comparisons still visit every byte with an accumulated XOR.

The focused Pure Simple boundary ratchet passed.  The authoritative census
changed:

- raw call sites: 20,725 -> 20,712
- caller files: 3,094 -> 3,093
- missing authority: 16,828 -> 16,815
- lexical unsafe: unchanged at 2,978
- function unsafe: unchanged at 919

This removes formatting, allocation, and foreign dispatch from pre-auth paths;
it adds no work to successful or rejected authentication.  Providers used by
lower transport/crypto owners remain without exact-artifact proof/signature
admission, so the wider SSH/SFFI surface is not globally verified or signed;
exact-artifact verified-and-signed admission remains 0.

## SSH daemon tokenization and provider-honesty checkpoint

The daemon owner removed 36 serial diagnostics, its raw byte accessor/append
calls, and one duplicate byte-to-text call.  Deferred-command tokenization now
converts the command to bytes once, indexes and appends in Pure Simple, and uses
one typed text-lift helper that rejects empty or failed token conversion.

The intentional RV64 boot-network bypass remains, because replacing it would
change the selected transport architecture.  Its bind and one-shot accept
providers now carry explicit FFI metadata, run in minimal lexical scopes, and
reject negative or non-`i32` descriptors after normalization.  No lookup,
allocation, or dispatch was added to accept polling.

Review also removed startup prose and diagnostics claiming an Ed25519 self-test
had passed.  No such self-test was invoked in this owner; configured credential
presence, exact 32-byte key lengths, and host-key policy are the actual current
admission checks.  The focused ratchet prevents restoring the unsupported
verification claim.

The focused static boundary ratchet passed.  The authoritative census changed:

- raw call sites: 20,712 -> 20,673
- missing authority: 16,815 -> 16,773
- lexical unsafe: 2,978 -> 2,981
- function unsafe: unchanged at 919

The hot command/accept paths are cheaper because raw diagnostics and per-byte
foreign work disappeared.  The boot TCP and text providers still lack exact-
artifact ABI/proof/signature evidence, and Ed25519 is not newly verified by
this checkpoint.  SSH and the wider SFFI surface remain not globally verified
or signed; exact-artifact verified-and-signed admission remains 0.

## SSH live cipher contract checkpoint

The SSH live cipher removed eleven secret-bearing serial diagnostics and its
raw byte accessor.  Key, IV, nonce, AAD, plaintext, ciphertext, tag, and packet
bytes are no longer hex-formatted on encrypt/decrypt paths, and byte reads use
an inline bounds-checked Pure Simple helper.

The three AES-256 providers now carry explicit FFI metadata and are called from
three minimal lexical scopes.  AES-256 requires a 32-byte key; AES-128 requires
16 bytes; both require a 12-byte IV/nonce and an exact bounded SSH GCM frame.
Encrypt output must be plaintext length plus the 16-byte tag.  The Rust decrypt
provider's status-prefixed contract is now enforced exactly: `0x00` is tag
mismatch, only `0x01` is success, and success length must equal ciphertext
length plus the status byte.  The direct packet provider must return a nonempty
payload no larger than the authenticated packet body.

Malformed short IVs previously became zero-padded nonces.  They now fail before
encryption/decryption rather than manufacturing nonce bytes.  The valid nonce
path also removes twelve repeated IV-length branches after its single exact-
length check.

The focused Simple/provider ratchet passed.  The authoritative census changed:

- raw call sites: 20,673 -> 20,661
- missing authority: 16,773 -> 16,758
- lexical unsafe: 2,981 -> 2,984
- function unsafe: unchanged at 919

The new validation is constant-time scalar/length comparison.  No allocation,
copy, lookup, lock, hashing, signature operation, or generic dispatch was added.
Exact provider artifact/proof/signature evidence remains absent, so the cipher
and wider SFFI surface are not globally verified or signed; exact-artifact
verified-and-signed admission remains 0.

## Synchronous SIMD SFFI facade checkpoint

`src/lib/nogc_sync_mut/simd.spl` has 48 direct calls to 47 `rt_simd_*`
symbols.  All 48 calls now carry minimal lexical `unsafe(ffi)` authority.  The
focused `nogc-sync-simd-sffi-authority.shs` audit passed and ratchets the call
and scope counts.  It also rejects per-call signature verification, symbol
lookup, locking, or generic FFI dispatch in these instruction-level hot paths.

The raw profile result previously mapped every unknown discriminant to
`SimdTier.scalar`, manufacturing a valid capability state from a provider
contract violation.  Unknown values now fail closed; the nine valid match arms
are unchanged.  Normal calls retain one direct foreign call and the same data
movement, allocation count, and asymptotic complexity.  No C/Rust replacement
for the Pure-Simple vector/ML-KEM algorithms was introduced.

The authoritative call census changed exactly as expected:

- missing authority: 17,689 -> 17,641
- lexical unsafe: 2,569 -> 2,617
- function unsafe: unchanged at 918

Native Rust providers lower several vector structures through scalar lanes and
out pointers, whereas the interpreter exposes typed `Value` structures.  This
can be a compiler-owned lowering convention, but the current source census is
not an ABI fingerprint or cross-lane proof.  Consequently these wrappers are
unsafe-bounded, not verified or signed.  No production optimizer or runtime
benchmark was available in this worktree; performance evidence is limited to
the unchanged direct-call source shape.  Verified-and-signed admission remains
0.
## SimpleOS socket facade SFFI checkpoint

`src/os/kernel/net/rt_net_socket_facade.spl` is a Pure-Simple socket owner over
19 boot/runtime declarations.  All declarations now carry explicit
`@unsafe(... ffi)` metadata and all 50 calls use minimal lexical `unsafe(ffi)`
scopes.  No C or Rust replacement was introduced.  The focused
`os-net-socket-sffi-authority.shs` audit passed and ratchets declaration and
call inventories while rejecting per-call admission, lookup, locks, and generic
dispatch.

The same checkpoint closes bounded-input defects before entering the provider:

- reject ports outside 0..65535 before `u16` conversion while preserving port
  zero for ephemeral binding;
- cap exact SSH reads at 35,016 bytes and reject provider chunks larger than
  the requested remainder;
- cap the generic socket read request at 16 MiB;
- reject plaintext SSH packet lengths above 35,000 bytes before allocation;
- validate cached-payload slice signs and subtraction-first extents before
  forming the end index.

These are O(1) guards.  Normal paths keep the same direct calls, loop
complexity, copies, and persistent socket layout; worst-case foreign-controlled
allocation is reduced.  The authoritative call census changed exactly as
expected:

- missing authority: 17,641 -> 17,591
- lexical unsafe: 2,617 -> 2,667
- function unsafe: unchanged at 918

The provider still uses legacy empty-array/empty-text error sentinels in APIs
that cannot distinguish transport failure from valid empty data.  Correcting
that requires an ABI-versioned `Result`/status contract across all consumers;
this checkpoint does not fabricate a local distinction.  No production
self-hosted runtime was available for executable optimizer or RSS evidence, so
the lane is unsafe-bounded, not verified.  Verified-and-signed admission
remains 0.
## Standard-library file I/O SFFI checkpoint

The synchronous file facade now has explicit authority on all 36 declarations
and minimal lexical scopes on all 47 calls.  Four previously unscoped calls in
the related mmap facade were also bounded; its seven declarations and seven
calls are now all explicit.  The focused `stdlib-file-io-sffi-contract.shs`
audit passed.

Provider review found and corrected contract defects rather than working around
them:

- `rt_file_get_size` is registered as `i64`; native now returns signed `i64`
  and uses `-1` for invalid descriptors, metadata failure, and overflow rather
  than fabricating zero.  Both Simple declarations now match.  The legacy
  `Option<i32>` facade narrows only representable values.
- `file_size()` now calls the actual `rt_file_size` provider instead of
  misinterpreting the modification-time `rt_file_stat` result as bytes.
- text, line-list, byte-array, and directory-list nil failures remain distinct
  from valid empty values in safe `Result` wrappers.  The explicitly `_unsafe`
  compatibility wrappers retain their documented empty sentinels.
- `is_dir()` now calls the semantic boolean provider instead of allocating a
  directory listing and returning the always-true expression `len >= 0`.
- `rt_dir_create` and `rt_dir_remove` now pass the required recursive boolean
  argument explicitly, eliminating an ABI register mismatch.

The authoritative census changed exactly as expected:

- missing authority: 17,591 -> 17,540
- lexical unsafe: 2,667 -> 2,718
- function unsafe: unchanged at 918

The focused Rust descriptor test passed (`1 passed`, 1,226 filtered) and now
distinguishes an empty file size of zero from invalid descriptor failure `-1`.
Normal file operations retain direct calls and their existing I/O complexity;
the semantic directory query removes a directory scan and result allocation.
No per-operation hashing, signature work, discovery, lock, or generic dispatch
was added.  Production Simple optimizer/performance evidence remains
unavailable in this worktree.  Glob/find/walk and some legacy unsafe helpers
still have empty-result ambiguity, so this lane is not globally verified or
signed; verified-and-signed admission remains 0.
## Debug/ptrace/DWARF SFFI checkpoint

`src/lib/nogc_sync_mut/sffi/debug.spl` has 43 raw declarations and calls.
Every call now has a minimal lexical `unsafe(ffi)` scope; the pre-existing raw
DWARF handle wrapper remains function-level unsafe.  The focused
`debug-sffi-authority.shs` audit passed.  It records 14 observed Rust debugger
providers and 29 declarations with no repository-owned provider.  Missing
debugger, ptrace, and DWARF providers remain raw/unsafe and link-fail-closed;
no nil/zero stub was added.

Breakpoint ABI review corrected three concrete defects:

- add now uses the provider's three-argument signature and signed ID/status
  result rather than passing an invented fourth ID argument;
- remove now declares its signed status result, and clear uses the actual
  `rt_debug_remove_all_breakpoints` symbol;
- the Rust add/remove/query providers reject null, negative/unrepresentable
  extents, invalid lines, and invalid UTF-8 instead of constructing unchecked
  slices and calling `from_utf8_unchecked`.

A semantic `rt_debug_has_breakpoint` provider was added without mutating hit
counters.  Boolean wrappers use an inline total 0/1 contract and fail closed on
invalid discriminants rather than treating every nonzero integer—including an
error sentinel—as true.  Nonexistent raw exports were removed from the facade.

The authoritative census changed as expected for the 42 previously missing
calls (the DWARF load call was already function-unsafe):

- missing authority: 17,540 -> 17,498
- lexical unsafe: 2,718 -> 2,760
- function unsafe: unchanged at 918
- distinct called symbols: 3,267 -> 3,266 after consolidating the clear symbol

The focused Rust breakpoint contract test passed (`1 passed`, 1,227 filtered).
Normal debugger state calls remain direct.  The new validation is limited to
breakpoint mutation/query boundaries and adds no hashing, signing, discovery,
generic dispatch, or long-lived allocation.  Ptrace/DWARF and 15 debugger
operations are still unavailable, so the module is not verified or signed;
verified-and-signed admission remains 0.

## Artifact-manifest signed-admission boundary checkpoint

The generic artifact manifest has one freestanding raw call: byte access while
hex-encoding its Pure Simple SHA-256 digest.  Its declaration and call now have
minimal `unsafe(ffi)` authority.  The wrapper requires an exact 32-byte digest
and a returned byte in 0..255 before encoding; invalid runtime behavior traps
instead of manufacturing an empty or malformed identity.

The loader-owned Ed25519 verifier now also rejects non-canonical image and
trust-root identities before signing-body construction.  Both must be exactly
64 lowercase hexadecimal characters.  Existing admission still requires a
three-field Ed25519 envelope, a 64-byte decoded signature, a private trusted
signer capsule, an exact trust-root hash, canonical signing bytes, and a Pure
Simple Ed25519 verification result.  The package-private receipt remains the
authority carrier; caller-supplied booleans cannot construct an executable
handle, and the verifier call precedes handle construction.

The focused `artifact-manifest-admission-contract.shs` ratchet passed.  The
authoritative call census changed by the one newly bounded accessor:

- missing authority: 17,259 -> 17,258
- lexical unsafe: 2,953 -> 2,954
- function unsafe: unchanged at 919

Hashing, trust-root lookup, locking, and signature verification remain
load-time admission work, not per-executable-call work.  The new identity
checks are two bounded 64-character scans before much more expensive Ed25519
verification and allocate no arrays.  No production self-hosted executable was
available for the signature fixtures.  This proves a local fail-closed source
shape, not that any exact provider artifact has a verified receipt; repository
verified-and-signed admission remains 0.

## SimpleOS Ed25519 Pure-Simple boundary checkpoint

`src/os/crypto/ed25519.spl` previously claimed to be Pure Simple while still
containing 45 raw calls: 41 unconditional `serial_println` diagnostics, three
runtime crypto-helper calls with no non-vendored C or Rust provider, and a
runtime byte-index helper.  The focused `ed25519-pure-boundary.shs` audit now
requires zero raw extern declarations and calls in this module.

The public Ed25519 implementation remains Pure Simple.  Native Simple array
indexing replaces the raw byte-index helper.  The phantom SHA-512/scalar helper
backend was removed; the canonical checked signature facade is compared
directly with the existing Pure Simple signature.  Exact 32-byte key and
64-byte signature contracts are enforced, provider disagreement returns an
error, and the `runtime_only` API no longer silently succeeds through a Pure
Simple fallback after provider failure.

All production tracing, signature hex formatting, and the 32-byte scalar probe
copy were removed.  Dual-run metadata is now constructed only after the normal
mode returns, eliminating its common-path empty-array allocation.  This removes
I/O and allocation from signing rather than adding checks to its inner scalar
or hash loops.

The authoritative census changed by removing all 45 former call sites:

- missing authority: 17,304 -> 17,259
- lexical unsafe: unchanged at 2,953
- function unsafe: unchanged at 919

This establishes the local Pure-Simple boundary and fail-closed result shape;
the production self-hosted binary was unavailable for an RFC 8032 executable
vector or optimizer run.  The checkpoint therefore does not prove the
Ed25519 arithmetic, compiler, loader, or exact artifact.  Repository
verified-and-signed admission remains 0.

## TLS 1.3 handshake SFFI checkpoint

All 49 raw calls in the TLS 1.3 handshake driver now have minimal lexical
`unsafe(ffi)` scopes.  The focused `tls13-handshake-sffi-contract.shs` ratchet
passed and uses an identifier-boundary matcher so ordinary names containing an
`rt_` substring are not counted as foreign calls.

Foreign-result review closed several fail-open and bounds defects:

- ServerHello and post-HRR payload lengths must be at least a handshake header,
  no larger than 18,432 bytes, and fit within the returned record before any
  subtraction or copy;
- ClientHello records must contain the five-byte TLS record header;
- the implemented handshake accepts only its documented
  `TLS_AES_128_GCM_SHA256` suite;
- X25519 keys, SHA-256 hashes, derived secrets, traffic keys/IVs, and Finished
  keys/data must have their exact contract lengths;
- foreign handshake messages must contain at least their four-byte header
  before body slicing;
- empty expected and received Finished values can no longer compare equal and
  authenticate a server.

The authoritative census changed exactly by the 49 newly bounded calls:

- missing authority: 17,353 -> 17,304
- lexical unsafe: 2,904 -> 2,953
- function unsafe: unchanged at 919

The valid path adds scalar length/discriminant comparisons only; it adds no
allocation, copy, lookup, lock, hashing, signature verification, discovery, or
generic dispatch.  A redundant post-validation Finished comparison was
removed.  The fixed bootstrap key path, remaining TLS call sites, provider
proof obligations, and exact-artifact signatures remain unresolved, so TLS is
not globally verified or signed; verified-and-signed admission remains 0.

## TLS 1.3 context-I/O call-authority checkpoint

The TLS 1.3 context owner retains 48 operation-specific raw declarations and
now places all 17 actual raw calls in minimal lexical `unsafe(ffi)` scopes.
The focused `tls13-context-sffi-contract.shs` ratchet passed and excludes
function-name substrings from its raw-call scan.

Review found an extent defect before the IPC receive boundary.  The direct
receive helper previously narrowed arbitrary `u64` lengths to `u32` and then
computed `max_len + 16` for the foreign receive allocation.  It now rejects
zero and values above the existing RFC 8446 record payload bound of 18,432
bytes before either operation.  Valid TLS records keep the same calls, copies,
loops, and allocation sizes.

The authoritative census changed exactly by the 17 newly bounded calls:

- missing authority: 17,370 -> 17,353
- lexical unsafe: 2,887 -> 2,904
- function unsafe: unchanged at 919

The new valid-path check is constant-time and prevents oversized work.  No
hashing, signing, discovery, lock, allocation, copy, or generic dispatch was
added.  The wider handshake driver still contains unbounded raw calls and the
TLS providers lack exact-artifact signed proof receipts, so the TLS family is
not globally verified or signed; verified-and-signed admission remains 0.

## HTTP/WebSocket call-authority checkpoint

The three legacy HTTP/WebSocket facades each retain 26 explicitly tagged raw
declarations and now place all 29 wrapper calls in minimal lexical
`unsafe(ffi)` scopes.  The focused `http-sffi-call-authority.shs` ratchet
passed: 78 declarations and 87 calls are covered without making the entire
safe-looking wrapper functions unsafe.

Provider inspection confirms that coverage remains partial.  Native C owns
GET, generic request, download, and client lifecycle/request operations; the
Rust interpreter owns GET and generic request.  The other declared operations
remain unsafe and link-fail-closed.  No zero, false, empty-text, or nil provider
stub was added.  The active native response reader's existing 64 MiB bound is
retained.

The authoritative census changed exactly by the 87 newly bounded calls:

- missing authority: 17,457 -> 17,370
- lexical unsafe: 2,800 -> 2,887
- function unsafe: unchanged at 919

Lexical capability scopes are compile-time metadata and add no network work,
allocation, copy, lookup, lock, branch, hashing, signing, or generic dispatch.
No production self-hosted optimizer or benchmark was available.  Missing
providers, ambiguous WebSocket empty-text receive semantics, TLS policy, and
artifact evidence remain unresolved, so the family is not globally verified
or signed; verified-and-signed admission remains 0.

## GLFW SFFI contract and dispatch checkpoint

The hosted GLFW facade has 40 raw declarations and 41 raw calls.  All
declarations now carry explicit FFI authority and all calls are covered by 24
minimal lexical scopes; the raw ARGB word-pointer path additionally requires
`raw_ptr`.  The focused `glfw-sffi-contract.shs` audit passed.

Provider and wrapper review corrected contract defects instead of converting
them to convenient values:

- invalid window handles now make `rt_glfw_should_close` return `-1`; the
  Simple wrapper accepts only the semantic 0/1 boolean domain;
- unavailable or invalid clipboard access returns null and lifts to `text?`,
  preserving a valid empty clipboard string as distinct from absence;
- window and frame dimensions are bounded to 8192 and frame input to 256 MiB
  before allocation or byte access;
- the Rust interpreter bridge caches each resolved typed-family symbol in a
  fixed atomic slot, eliminating its prior `dlsym` on every event/frame call.

The authoritative census changed exactly by the 41 newly bounded calls:

- missing authority: 17,498 -> 17,457
- lexical unsafe: 2,760 -> 2,800
- function unsafe: 918 -> 919 (the raw-pointer method is now explicitly unsafe)

GNU C11 syntax validation and the focused Rust GLFW bridge tests passed.  The
cached path adds no hashing, signature operation, mutex, allocation, or symbol
lookup; its remaining signature-table scan is fixed at 41 entries and predates
this checkpoint.  No production self-hosted optimizer or benchmark was
available.  GLFW lifetime, callback, and artifact-evidence obligations remain
unsafe, so this module is not globally verified or signed; verified-and-signed
admission remains 0.

## MIR-to-LLVM core codegen authority checkpoint

The core textual LLVM lowering now confines its seven used foreign ABI
families to mandatory-inline lexical `unsafe(ffi)` owners.  The environment
read contract is truthfully nullable, and the unused `rt_string_len`
declaration was removed instead of granting unused authority.

This is a hot compiler path: enum discriminant/payload and tuple projection
run during instruction lowering, while string-builder appends run during IR
emission.  The focused static ratchet therefore pins every owner as
`@always_inline` and preserves the exact existing primitive-call counts.  No
validation scan, table dispatch, lookup, allocation, copy, hash, lock, or new
loop was added.

The authoritative census changed exactly by routing 41 former direct calls
through seven owners:

- raw call sites: 19,119 -> 19,085
- missing authority: 14,930 -> 14,889
- lexical unsafe: 3,270 -> 3,277
- function unsafe: unchanged at 919

The focused audit also confirms all seven symbols are present in both the
typed native registry and interpreter registration.  That is provider
coverage, not proof: tagged-value layout, handle validity, exact artifact
identity, signature trust, and evidence admission remain unresolved.  No
production self-hosted optimizer or benchmark was available, so this module
and the wider SFFI estate are not globally verified or signed;
verified-and-signed admission remains 0.

## AES-128-GCM canonical/NVFS authority checkpoint

The canonical AES-128-GCM implementation and its divergent NVFS adapter now
consolidate runtime array allocation through mandatory-inline owners while
preserving every remaining capacity hint. Unchecked byte access and validated
crypto cores carry explicit FFI authority; checked public wrappers
retain the existing API. Encryption fails closed on invalid fixed key/nonce
extents because its legacy array return cannot encode an error. Decryption
rejects invalid key, nonce, and tag extents with typed `Aes128GcmResult.Err`
before entering the 16-byte constant-time tag comparison.

Provider review found that the interpreter's out-parameter AES block helper
cannot mutate the caller's array but reported success. The NVFS adapter now
uses the existing pure-result AES block provider, requires an exact 16-byte
result, and passes the already validated key directly. It no longer builds an
unused 176-byte expanded schedule, allocates/copies a 16-byte key per block, or
allocates/fills a redundant zero output array. The dead AES table providers
and unused serial byte-dump surface were removed. The focused
`aes128-gcm-sffi-authority.shs` audit passed and pins the allocation counts,
fixed input guards, constant-time accumulator, provider coverage, and absence
of the broken out-parameter path.

The authoritative census changed as follows:

- raw call sites: 18,671 -> 18,636
- distinct called symbols: 3,260 -> 3,257
- caller files: unchanged at 3,088
- missing authority: 13,768 -> 13,728
- lexical unsafe: 3,411 -> 3,413
- function unsafe: 1,492 -> 1,495

The hot GCM/GHASH loop counts are unchanged. Allocation capacity and linear
copy behavior are retained. The NVFS operation removes one 176-byte expanded
schedule; each AES block removes one 16-byte key allocation/copy and 16 zero
pushes while the pure-result provider owns the required output allocation. No
lookup, lock, hash, signature operation, or
generic dispatch was added. The one executable NIST-vector test
attempt was blocked before loading the spec by the unrelated hosted
environment parse bug recorded in
`doc/08_tracking/bug/aes128_gcm_verification_blocked_by_env_access_parse_2026-08-25.md`.
Therefore executable verification is missing, exact artifact/signature
evidence remains absent, and verified-and-signed admission remains 0.

## x86_64 boot network-services authority checkpoint

The x86_64 boot network probe's seven baremetal runtime families now carry
explicit FFI authority and route through seven mandatory-inline owners. The
provider-reported PCI count is accepted only in the concrete C runtime's
0-through-32 device range before enumeration. Negative or excessive counts
fail closed as network unavailable; invalid field projections remain unable
to match the exact Ethernet/VirtIO identifiers.

Initialization, TX, RX, and statistics probes retain signed status values and
must all be nonnegative before readiness becomes exactly `1`. The public
readiness API remains semantic `bool`; no numeric boolean workaround or
zero/true provider fallback was introduced. The focused
`x86-64-boot-services-sffi-authority.shs` audit passed. It records that logging
is interpreter-only and that all six PCI/network operations are absent from
both hosted typed registries; this baremetal provider gap is not proof.

The authoritative census changed as follows:

- raw call sites: 18,636 -> 18,615
- distinct called symbols: unchanged at 3,257
- caller files: unchanged at 3,088
- missing authority: 13,728 -> 13,700
- lexical unsafe: 3,413 -> 3,420
- function unsafe: unchanged at 1,495

Runtime complexity remains `O(min(provider_count, 32))`. Mandatory inlining
preserves direct primitive calls; the only new runtime work is one constant
range check before enumeration. There is no allocation, copy, lookup, lock,
hash, signature operation, generic dispatch, or per-device validation branch.
The executable system test remains blocked by the previously recorded hosted
environment parser failure. Exact x86 provider artifact identity, signed
admission, and device-level proof remain absent, so verified-and-signed
admission remains 0.

## Direct FAT32 boot-reader authority checkpoint

The direct FAT32 boot reader's four used runtime families now carry explicit
FFI authority and route through mandatory-inline owners. Two unused runtime
declarations were removed. The packed-byte file-chain path retains its exact
requested-size allocation, one checked typed-byte append per copied byte, the
512 MiB whole-file ceiling, bounded cluster count, Floyd-style cycle guard,
and reused DMA scratch buffer.

The prior `_vfs_boot_byte` out-of-range fallback manufactured byte zero, which
can be interpreted as an end-of-directory marker. It now fails closed. The
boot-sector length check was moved before diagnostic byte reads so malformed
short sectors still produce the existing typed `Err("boot-sector-short")`
rather than reaching that assertion. The focused
`direct-fat32-boot-sffi-authority.shs` audit passed. It records three providers
in both typed registries and the expected interpreter-only boot logger; this
registration coverage is not signature or proof evidence.

The authoritative census changed as follows:

- raw call sites: 18,615 -> 18,592
- distinct called symbols: unchanged at 3,257
- caller files: unchanged at 3,088
- missing authority: 13,700 -> 13,673
- lexical unsafe: 3,420 -> 3,424
- function unsafe: unchanged at 1,495

The hot file-copy path has unchanged `O(size)` complexity, allocation count,
copy count, and one provider status branch per byte. Mandatory inlining avoids
new dispatch overhead. No lookup, lock, hash, signature operation, generic
marshalling, or per-cluster allocation was added. Legacy array-return lookup
helpers still conflate not-found/read failure with valid empty data and the
DMA/MMIO artifact chain remains unsigned and unproved, so this module is not
globally verified or signed; verified-and-signed admission remains 0.

## Legacy SQLite wrapper authority checkpoint

The three legacy SQLite wrapper mirrors now expose their existing unsafe
reality consistently: each has 27 unsafe raw declarations and 24 exact unsafe
wrapper owners covering all 26 call sites. The wrappers retain raw integer
handles, manual finalization, unchecked column/bind indices, and ambiguous
empty/false/zero error conventions, so promoting them to safe `Option`/`Result`
APIs would require a separate breaking migration. PureDatabase remains the
preferred safe in-tree backend.

The focused `sqlite-legacy-wrappers-sffi-authority.shs` audit passed. It pins
all three mirrors, keeps the two data-only row helpers safe, and confirms that
all 27 SQLite providers are interpreter-registered but absent from the typed
native registry. Raw declarations remain exported for existing internal
database layers, but their unsafe declarations and unsafe callers prevent this
checkpoint from presenting them as verified safe.

The authoritative census changed exactly by the 78 newly bounded calls:

- raw call sites: unchanged at 18,592
- distinct called symbols: unchanged at 3,257
- caller files: unchanged at 3,088
- missing authority: 13,673 -> 13,595
- lexical unsafe: unchanged at 3,424
- function unsafe: 1,495 -> 1,573

Annotations add no runtime work. No allocation, copy, loop, query, lookup,
lock, branch, hash, signature operation, generic dispatch, or forced inlining
was added. Handle ownership, query-next done/error separation, nullable column
text, exact SQLite artifact identity, typed-native registration, and signed
evidence remain unresolved. Therefore these wrappers and the wider SFFI estate
are not globally verified or signed; verified-and-signed admission remains 0.

## VFS boot-state authority checkpoint

The canonical VFS boot-state owner's two used runtime families now carry
explicit FFI authority and route through two mandatory-inline owners. Five
unused runtime declarations were removed. The ELF readiness predicate retains
one four-byte extent guard followed by exactly four inline byte reads; no
per-byte loop, allocation, or copy was introduced. Boot readiness remains a
semantic `bool`, and the existing pure-Simple NVMe/FAT32 commit ordering is
unchanged.

The focused `vfs-boot-state-sffi-authority.shs` audit passed. It confirms that
the byte accessor is present in both typed registries while the boot logger is
interpreter-only. This is registration coverage, not proof or signed artifact
admission.

The authoritative census changed as follows:

- raw call sites: 18,592 -> 18,568
- distinct called symbols: unchanged at 3,257
- caller files: unchanged at 3,088
- missing authority: 13,595 -> 13,569
- lexical unsafe: 3,424 -> 3,426
- function unsafe: unchanged at 1,573

Annotations and mandatory inlining preserve direct-call behavior. No runtime
branch, allocation, copy, lookup, lock, hash, signature operation, generic
dispatch, or boot-state transition was added. MMIO/DMA ownership and mutex
providers remain separate unverified boundaries, and exact artifacts/evidence
remain unsigned. This module and the wider estate are not globally verified
or signed; verified-and-signed admission remains 0.

## POSIX dynamic-call bridge authority checkpoint

All 14 raw declarations in the POSIX dynamic-call bridge now carry explicit
`ffi, raw_ptr` authority. The exact provider-query and CLI-command owners and
all seven generic integer-only call owners carry the same caller-visible
authority. A null symbol address is now rejected as negative failure while an
existing negative loader diagnostic is preserved; null can no longer reach a
generic call and appear as integer zero.

The exact two bridge families retain their existing bounded allocations,
request/result cleanup, decoded-size checks, and status agreement checks. The
focused `posix-dynlib-sffi-authority.shs` audit passed and records provider
coverage as 6 symbols in both typed registries, 1 in one registry, and 7 in
neither. Registration does not establish arbitrary target ABI compatibility,
handle lifetime, artifact identity, or signature trust.

The authoritative census changed exactly by the 25 newly bounded calls:

- raw call sites: unchanged at 18,568
- distinct called symbols: unchanged at 3,257
- caller files: unchanged at 3,088
- missing authority: 13,569 -> 13,544
- lexical unsafe: unchanged at 3,426
- function unsafe: 1,573 -> 1,598

The null hardening broadens one existing constant branch and adds no
allocation, copy, lookup, lock, hash, signature operation, or dispatch. The
generic wrappers still perform symbol-name resolution on every call and use
an all-integer ABI; this pre-existing cost and ABI unsafety remain visible and
make them ineligible for hardened/critical hot paths. Typed cached thunks and
signed provider admission remain unimplemented, so verified-and-signed
admission remains 0.

## Package-service logging authority checkpoint

The package service already imported the canonical kernel logging API but
duplicated an interpreter-only `serial_println` declaration and called it 25
times directly. Those calls now use `log_raw_println`, and the redundant raw
declaration is removed. The canonical logger's two raw calls are isolated by
one mandatory-inline lexical `ffi` owner; the raw declaration itself now also
records explicit authority.

The focused `pkg-service-logging-sffi-authority.shs` audit passed. It pins the
25 package-service calls, the single canonical declaration, two canonical raw
call sites, mandatory inlining, and current provider coverage (0 typed-native,
1 interpreter). Provider registration remains an inventory fact rather than
proof or signed admission.

The authoritative census changed as follows:

- raw call sites: 18,568 -> 18,542
- distinct called symbols: unchanged at 3,257
- caller files: 3,088 -> 3,087
- missing authority: 13,544 -> 13,517
- lexical unsafe: 3,426 -> 3,427
- function unsafe: unchanged at 1,598

The routing preserves semantic `bool` and list APIs. The mandatory-inline
owner adds no runtime allocation, copy, lookup, lock, hash, signature check,
or dispatch; raw-line logging remains O(1) apart from the existing foreign
output cost. Serial output is still interpreter-only and its exact artifact is
not authenticated. The wider SFFI estate is not globally safe, verified, or
signed; verified-and-signed admission remains 0.

## Bare-metal HTTP canonical network-owner checkpoint

The boot HTTP server duplicated seven socket declarations and a raw logger even
though the canonical pure-Simple socket facade and kernel logger already own
those boundaries. The duplicates are removed and HTTP now imports both owners.
The one remaining byte-array-to-text lift has explicit `ffi` authority and a
lexical wrapper that rejects a non-empty input becoming empty output.

Two concrete resource/error defects were also fixed. A socket is now closed if
bind or listen fails, and both plaintext and TLS response loops observe the
canonical facade's exact-write result instead of continuing after a failed or
partial send. Semantic accept/handled booleans are unchanged. Existing receive
chunk, total-request, receive-iteration, and keepalive limits remain intact.

The focused `http-baremetal-sffi-authority.shs` audit passed. It pins canonical
owner imports, the single remaining lexical raw lift, exact-send checks,
failure cleanup, loop bounds, and the lift's interpreter-only provider status.
Registration still does not prove the native/freestanding ABI or authenticate
the provider artifact.

The authoritative census changed as follows:

- raw call sites: 18,542 -> 18,519
- distinct called symbols: unchanged at 3,257
- caller files: unchanged at 3,087
- missing authority: 13,517 -> 13,493
- lexical unsafe: 3,427 -> 3,428
- function unsafe: unchanged at 1,598

Canonical socket calls retain their existing linear scan over the bounded
active-socket table and bounded network operations; importing the owner does
not add another dispatch layer. The text validator is mandatory-inline and
the new checks are constant branches; no buffer copy,
allocation, hash, signature check, lock, library search, or generic dispatch
was added. The text lift remains interpreter-only, exact artifacts remain
unsigned, and the wider SFFI estate is not globally safe or verified;
verified-and-signed admission remains 0.

## Legacy FTP wrapper authority checkpoint

All 25 FTP/FTPS declarations already described themselves as unbacked raw
interfaces, but their 25 direct wrappers remained apparently safe. No FTP
symbol is registered in either the typed-native registry or interpreter
registry, and no provider, handle ownership contract, error contract, TLS
policy, artifact identity, or signature evidence exists. Each exact wrapper is
therefore now explicitly `unsafe(ffi)` rather than pretending that handle
positivity or a boolean return establishes safety.

The focused `ftp-sffi-authority.shs` audit passed. It pins 25 declarations, 25
direct call sites, 25 wrapper authorities, zero registered providers, and the
absence of new wrapper layers or forced inlining. Existing semantic booleans,
text/list results, and the legacy `-1` size sentinel are preserved; changing
those APIs to `Result` without a provider error ABI would invent semantics.

The authoritative census changed as follows:

- raw call sites: unchanged at 18,519
- distinct called symbols: unchanged at 3,257
- caller files: unchanged at 3,087
- missing authority: 13,493 -> 13,468
- lexical unsafe: unchanged at 3,428
- function unsafe: 1,598 -> 1,623

Annotations add no runtime branch, allocation, copy, lookup, lock, hash,
signature operation, dispatch, or data-layout change. This adapter remains
unusable in safe or critical code until a real provider and typed contract are
implemented and admitted. Verified-and-signed admission remains 0.

## Legacy SSH/SFTP wrapper authority checkpoint

The 23 SSH/SFTP declarations were already documented as unbacked and absent
from the runtime, typed-native registry, and interpreter registry, but their 23
direct wrappers still appeared safe. Those exact wrappers now carry explicit
`unsafe(ffi)` authority. This makes the absent provider, unknown host-key and
credential policy, unbounded/ambiguous output, handle ownership, partial-write,
path, timeout, and metadata obligations caller-visible.

The focused `ssh-sffi-authority.shs` audit passed. It pins all 23 declarations,
23 call sites, 23 wrapper authorities, zero registered providers, and the
absence of new wrapper layers or forced inlining. Existing semantic booleans,
text and tuple results, invalid handles, zero-write sentinel, and fabricated
legacy metadata remain unchanged because a safe `Result` mapping cannot be
defined until a real provider supplies an authoritative error ABI.

The authoritative census changed as follows:

- raw call sites: unchanged at 18,519
- distinct called symbols: unchanged at 3,257
- caller files: unchanged at 3,087
- missing authority: 13,468 -> 13,445
- lexical unsafe: unchanged at 3,428
- function unsafe: 1,623 -> 1,646

Annotations add no runtime branch, allocation, copy, lookup, lock, hash,
signature operation, dispatch, or data-layout change. This dead legacy adapter
is not safe or critical-admissible; verified-and-signed admission remains 0.

## Legacy compression/archive wrapper authority checkpoint

All 24 gzip, deflate, zip, tar, and tar-gzip declarations are unbacked and
absent from both typed registries. Their 24 direct wrappers plus four
convenience wrappers now carry explicit `unsafe(ffi)` authority. This exposes
the unresolved binary-in-text representation, decompression expansion, archive
traversal/link/overwrite, handle lifecycle, partial status, and output ownership
obligations instead of presenting the adapter as safe.

The focused `compress-sffi-authority.shs` audit passed. It pins 24 declarations,
24 call sites, 28 wrapper authorities including the four transitive APIs, zero
registered providers, and no added wrapper or forced-inline layer. Existing
boolean status comparisons, text/list results, handles, and sentinels remain
unchanged because no real provider error ABI exists from which to derive safe
`Result` semantics or bounded decompression behavior.

The authoritative census changed as follows:

- raw call sites: unchanged at 18,519
- distinct called symbols: unchanged at 3,257
- caller files: unchanged at 3,087
- missing authority: 13,445 -> 13,421
- lexical unsafe: unchanged at 3,428
- function unsafe: 1,646 -> 1,670

Annotations add no runtime branch, allocation, copy, lookup, lock, hash,
signature operation, dispatch, or data-layout change. This adapter remains
unsafe and critical-ineligible; verified-and-signed admission remains 0.

## SOCKS5 Pure Simple boundary checkpoint

The SOCKS5 framing module described itself as Pure Simple but performed 20 raw
byte-index calls and two raw text-to-byte calls in addition to one byte-to-text
lift. Guarded native array indexing now replaces the byte accessor, and the
canonical pure-Simple `text_to_bytes` owner replaces the encoding calls. The
only remaining foreign call is the domain byte-to-text lift; it is explicitly
unsafe, lexically scoped, and rejects non-empty bytes becoming empty text.

Two wire correctness defects were fixed without changing result booleans.
Domain names must contain 1..255 encoded bytes, and username/password fields
must fit the protocol's one-octet length. Oversized builders now fail closed
instead of truncating the length modulo 256; a zero-length parsed domain is
rejected. Existing parser extent checks continue to dominate native indexing.

The focused `socks5-pure-simple-sffi-authority.shs` audit passed. It pins the
single remaining raw declaration/call, pure-Simple owners, one-octet bounds,
guarded port reads, and the remaining lift's presence in both typed registries.
Both maintained SOCKS5 specs now cover zero-length domain rejection.
Registration does not authenticate either provider artifact.

The authoritative census changed as follows:

- raw call sites: 18,519 -> 18,497
- distinct called symbols: unchanged at 3,257
- caller files: unchanged at 3,087
- missing authority: 13,421 -> 13,398
- lexical unsafe: 3,428 -> 3,429
- function unsafe: unchanged at 1,670

Native indexing removes foreign call dispatch from the parser loops. Encoding
retains the same single byte-array construction per field, and the required
length checks are constant branches; no additional copy, allocation, lookup,
lock, hash, signature operation, or generic dispatch was added. The one text
lift and exact artifacts remain unverified/unsigned, so verified-and-signed
admission remains 0.

## LLVM target-machine mirror authority checkpoint

The canonical synchronous SFFI target module, asynchronous SFFI mirror, and
compatibility FFI mirror all invoke LLVM through cached but untyped all-integer
dynamic thunks. Every one of their 20 target initialization, target-machine,
pass-manager, and memory-buffer APIs now carries caller-visible
`unsafe(ffi, raw_ptr)` authority. The three mirror bodies are mechanically
identical apart from ownership namespace/header spelling.

Three real C-string bugs were fixed in every mirror: target triples passed to
`LLVMGetTargetFromTriple`, output filenames passed to
`LLVMTargetMachineEmitToFile`, and pass pipelines passed to `LLVMRunPasses` now
use scoped NUL-terminated text. The asynchronous mirror also gains the
canonical allocation-failure cleanup for target/error/buffer out-pointers,
preventing null pointer writes and partial-allocation leaks.

The focused `llvm-target-sffi-authority.shs` audit passed. It pins 3 mirrors x
20 authorities, the three terminators, null-allocation cleanup, normalized
mirror equality, and both-registry coverage for all five underlying
allocation/pointer/generic-call primitives. Registration is not proof of LLVM
signature compatibility or artifact authenticity.

The authoritative census changed as follows:

- raw call sites: 18,497 -> 18,501 (four required failure-cleanup calls added)
- distinct called symbols: unchanged at 3,257
- caller files: unchanged at 3,087
- missing authority: 13,398 -> 13,354
- lexical unsafe: unchanged at 3,429
- function unsafe: 1,670 -> 1,718

The generic bridge's existing cached symbol lookup remains unchanged; no new
lookup, lock, hash, signature check, or dispatch is introduced. Each corrected
C-string adds one scoped allocation/copy only on cold target lookup, emission,
or pass-pipeline setup—not per IR instruction. The four extra raw calls occur
only during allocation failure cleanup.

The older combined `ffi/llvm_instructions.spl` compatibility surface was then
reviewed separately. Its duplicated 20 target APIs now carry the same unsafe
authority, C-string termination, and partial-allocation cleanup. No current
source consumer was found, but dead compatibility code is not treated as safe.
The focused audit now covers all four target surfaces. This follow-up does not
change the call census because the combined module imports through the legacy
`ffi` namespace, which the intentionally bounded source census does not classify
as an SFFI import; resolved HIR remains required to close that inventory gap.

Typed thunks and signed LLVM admission remain unresolved;
verified-and-signed admission remains 0.

## Legacy gamepad wrapper authority checkpoint

All 20 gamepad externs lack typed-native and interpreter providers. The 15
direct operation wrappers and four transitive stick/trigger/rumble helpers now
carry caller-visible `unsafe(ffi)` authority; the two pure deadzone math helpers
remain safe. Unknown context/event ownership, event discriminants, tuple and
floating-point ABI layout, runtime-owned text, rumble mutation, and error
semantics therefore no longer appear verified.

The focused `gamepad-sffi-authority.shs` audit passed. It pins 20 declarations,
20 raw call sites, 19 dependent wrappers, two safe pure-math helpers, zero
registered providers, and the absence of new wrapper or forced-inline layers.
Existing semantic booleans, floating values, invalid-event structs, and legacy
sentinels remain unchanged because there is no provider contract from which to
derive safe `Option` or `Result` semantics.

The authoritative census changed as follows:

- raw call sites: unchanged at 18,501
- distinct called symbols: unchanged at 3,257
- caller files: unchanged at 3,087
- missing authority: 13,354 -> 13,334
- lexical unsafe: unchanged at 3,429
- function unsafe: 1,718 -> 1,738

Annotations add no branch, allocation, copy, lookup, polling, lock, hash,
signature operation, dispatch, or data-layout change. This adapter remains
unsafe and critical-ineligible; verified-and-signed admission remains 0.

## Image-builder canonical I/O owner checkpoint

The image builder's 24 private process/file/directory calls now route through
eight canonical `std.io_runtime` owners. Two exact owners were added because
the existing convenience APIs intentionally normalized away distinctions this
security-sensitive builder needs: `file_size_signed` preserves negative
failure, and `dir_list_optional` preserves nil provider/read/allocation failure
separately from an empty directory. The process tuple owner is mandatory-inline
to avoid an extra aggregate-return frame.

Exact one-call text/byte writes, file existence, directory creation/existence,
the 120-second disk-build timeout, and the 15-second tool-probe timeout remain
unchanged. The recursive rootfs validator explicitly unwraps a successfully
listed directory only after rejecting nil, retaining its depth, entry-count,
allocation-overflow, and partition-capacity checks.

The focused `image-builder-sffi-authority.shs` audit passed. It pins zero local
extern declarations, 24 canonical calls, exact status/nullable behavior,
mandatory process inlining, original timeout values, and both-registry coverage
for all eight underlying providers. Registration remains weaker than signed
artifact admission or ABI proof.

The authoritative census changed as follows:

- raw call sites: 18,501 -> 18,479
- distinct called symbols: unchanged at 3,257
- caller files: 3,087 -> 3,086
- missing authority: 13,334 -> 13,310
- lexical unsafe: 3,429 -> 3,431
- function unsafe: unchanged at 1,738

The 24 duplicate raw calls become two centralized mandatory-inline raw calls,
so the net raw count falls by 22. No retry, scan, loop, filesystem operation,
buffer allocation/copy, lookup, lock, hash, signature operation, or generic
dispatch was added. The image providers and produced artifact are still not
cryptographically admitted by this source change; verified-and-signed remains
0.

## Privileged CPU SFFI removal checkpoint

The ARM32, ARM64, and RV32 CPU owners declared 63 `rt_*` functions for system
register access, barriers, TLB invalidation, interrupt masking, and wait
instructions. The authoritative extern census classified sampled identities
as genuinely missing, while generated x86 example providers retained weak
nil/no-op substitutes. The declarations therefore described neither a safe
nor a functional portable ABI.

The three target owners now emit 60 direct target instructions inside one
`inline_asm` capability region per operation. Three unused ARM32 FIQ-only
declarations disappear, and the two-call split ARM32 MPIDR reconstruction is
replaced by the architecture's single 32-bit MRC read. ARM64 DAIF changes use
their required immediate forms instead of pretending that immediate is a
general scalar ABI.

This removes foreign dispatch rather than adding validation to a hot path:
each operation remains O(1), allocation-free, copy-free, lookup-free, and
lock-free, with no per-call hashing or signature work. It does not prove the
instruction is legal at the caller's exception level, compiler operand
lowering, or hardware behavior. Each operation remains explicitly unsafe at
the smallest `inline_asm` boundary and is not a signed/admitted artifact. The
focused ratchet is source-reviewed only and was not executed in this tranche.

The 114 matching weak/no-op definitions were also removed from the two
checked-in x86 SimpleOS example provider snapshots. Six declaration identities
had no matching snapshot definition; unrelated ARM/RV32 runtime helpers remain
untouched.

### RISC-V 64 follow-up

The RV64 CPU owner had ten scalar SFFI declarations backed only by its
freestanding C boot object. Its generic CSR read/write/set/clear provider used
a runtime switch even though all Simple call sites supplied compile-time CSR
identities. The owner now emits 30 exact named instructions directly and the
91-line duplicate C dispatch implementation is removed.

This changes dynamic switch-plus-call CSR operations to one instruction while
preserving the HAL surface and explicit `inline_asm` authority. Required
memory clobbers retain compiler ordering without emitting hardware work. No
allocation, copy, lookup, hash, lock, signature check, or generic dispatch is
added. The RV64 compiler/privilege/hardware path is still source-reviewed only,
unsigned, and unverified.

## Architecture context and timer checkpoint

ARM32, ARM64, and RV32 context transfer each retain three target-assembly
declarations. They are not safe: the current methods pass addresses of by-value
context copies, so source-state persistence is unproved, and the providers lack
complete maintained registry and signed-artifact admission. All nine raw
declarations, nine calls, and nine caller-visible save/restore/switch methods
now carry explicit `ffi, raw_ptr` authority. RV32 wrong-architecture restore
now panics instead of silently succeeding. Initial stack pointers are aligned
once at context construction (8 bytes on ARM32, 16 on ARM64/RV32), adding no
per-switch work. The by-value ABI remains a recorded blocker, not a fixed or
verified path.

The ARM timer owners took the opposite route. Thirteen unbacked timer
declarations are removed and replaced by ten exact direct instructions. ARM32
CNTPCT is now one MRRC operation with two outputs instead of two foreign calls
that could observe different counter instants. Twenty-two matching weak nil/no-
op example definitions are removed. Timer reads/writes remain O(1), allocation-
free, lookup-free, and direct; memory clobbers add compiler ordering but no
runtime instruction. Cross-target assembly and hardware behavior remain
unverified and unsigned.

## User-entry and VirtIO input authority checkpoint

ARM32 and ARM64 privilege-transfer owners expose six target-specific scalar
declarations. Their token, recorded-handoff, address-space, assembly-control,
and non-returning assumptions are not represented by ordinary scalar types or
bound to admitted artifacts. All declarations and the four dependent wrapper
surfaces now carry `unsafe(ffi)` authority, and each raw call is lexically
confined. Existing preflight, token/reap equality, and failure statuses remain
unchanged; annotations add no transfer-path work.

ARM64 and RV64 VirtIO input each expose seven calls: initialization, polling,
and five projections from provider-global event state. Polling followed by
independent projections is not an atomic snapshot and cannot distinguish queue
corruption from no event. All fourteen declarations and four dependent wrappers
are now explicitly unsafe. Poll accepts only the provider's exact ready value
`1`; other values do not fabricate an event. The call topology remains one poll
plus five projections with no new allocation, copy, lookup, hash, lock,
signature operation, retry, or dispatch.

The required follow-up is a single stack status/out descriptor returning
`Result<Option<Event>, SffiError>`, reducing six calls to one. Until that ABI
and exact artifacts are admitted, these surfaces remain unsafe, unsigned, and
unverified. The focused ratchet was source-reviewed only and not executed.

## SBI and ARM32 boot-topology checkpoint

The RV32 SBI tuple declaration has no production provider. RV64 has a direct,
libc-free C ecall leaf, but neither the leaf nor its by-value return layout is
bound to an exact signed provider artifact. ARM32 boot topology is backed only
by a target example provider that exposes one immutable boot-global address as
two 16-bit reads. These six raw declarations are now explicitly `unsafe(ffi)`
and each call is confined to the smallest lexical capability region.

Both RV64 extension probes previously returned `true` from a nonzero value even
when the SBI error field reported failure. They now require success and a
nonzero value, preserving `bool` as the public result rather than converting it
to a numeric workaround. The legacy IPI path now passes the address of a live
stack mask word instead of treating the mask value as an address. Its CLINT
fallback honors `hart_mask_base`, rejects unrepresentable hart IDs, and stops
when the remaining mask becomes zero.

The changed call paths remain O(1) for probes and topology reads. IPI fallback
is O(highest-set-bit), improved from an unconditional 64 iterations. No heap
allocation, payload copy, name lookup, generic dispatch, lock, hash, or
signature operation was added. Source tags and a static ratchet are not proof
of ABI, firmware, compiler, hardware, or signed-artifact admission; RV32 stays
provider-blocked and verified-and-signed remains zero.

The full provider-aware inventory measured 11,370 `rt_*` declarations across
3,035 symbols: 2,798 declarations are unsafe-tagged, 8,323 are untouched, and
zero are signed-admitted. Its provider-language output is a disjoint set of
language combinations because one declaration can have C, Rust-export, and
Rust-interpreter providers simultaneously; the leading combination contains
5,622 declarations. This is the correct representation for parity analysis and
must not be collapsed into overlapping per-language totals without an explicit
multi-provider accounting rule.

## RISC-V cache-maintenance checkpoint

The shared CMO module exposes eight untagged `rt_riscv64_*` instruction leaves.
RV64 has matching libc-free C providers; RV32 imports the same wrappers but has
no matching target provider. All eight declarations and calls are now confined
to explicit `unsafe(ffi)`. The RV32 mismatch remains an open blocker rather than
being hidden behind a fabricated or generic fallback.

Three pure count helpers previously iterated once per cache line and could loop
forever when given a zero stride. They now use O(1) ceiling division, return
zero for disabled/empty/zero-stride inputs, and saturate at `u32::MAX` instead
of wrapping. RV32/RV64 production range loops now reject wrapping ranges before
the first CMO and use a last-address termination test that cannot overflow.

The production loop still performs exactly one foreign instruction call per
covered line. The preflight adds constant work once per range; there is no new
allocation, copy, registry/name lookup, generic dispatch, lock, hash, signature
operation, retry, or per-line admission work. Source checks cannot promote
these unsigned providers to verified or signed.

The focused ratchet passed, all three production modules passed bootstrap-seed
type checking, and the existing HalCache spec passed 18/18 examples in 150 ms.
Optimizer analysis reported no allocation or general-pattern finding; the one
actionable per-line issue, RV64 stride widening, is now hoisted once per range.
The available tool identified itself as a Rust bootstrap seed, so none of this
is self-hosted or cross-target verification.

## Canonical bare-metal MMIO checkpoint

Interrupt, allocator, syscall, and SBI modules duplicated 15 declarations of
the same six `rt_mmio_read/write_u8/u16/u32` identities. The providers are real
volatile pointer leaves in the bare-metal C runtime and Rust interpreter, but
an arbitrary address can fault, alias ordinary RAM, trigger device side
effects, or violate alignment and ordering. Provider presence is not a safety
or signed-artifact proof.

One canonical no-allocation owner now holds the six declarations, each tagged
`unsafe(ffi, raw_ptr)`, and exposes six inline wrappers with one lexical raw
call. Four consumers import those wrappers; their 15 duplicate declarations
and direct raw calls are removed. This reduces raw declaration identities by
nine while keeping policy and address construction in Pure Simple.

Inlining preserves one direct provider call per access. There is no added
allocation, copy, name/registry lookup, generic dispatch, lock, hash, signature
check, retry, or compatibility branch. Alignment/range/device authority remains
the caller's unsafe obligation until typed MMIO regions and exact provider
admission exist.

The Rust interpreter provider also previously cast negative, null, and
misaligned integers directly to volatile pointers. Its six u8/u16/u32 leaves
now share one inline checked lift that rejects non-positive, host-width-invalid,
and width-misaligned addresses before entering Rust `unsafe`. Error formatting
allocates only on rejected calls; the valid interpreter path adds scalar
comparisons, while native bare-metal remains branch-free.

The focused Rust unit test is currently blocked before its target compiles by
unrelated `simple-runtime` `E0432` export drift in spin-loop, TLS, and UDP
families. No fallback package or feature exclusion was used, and the Rust MMIO
provider is not labeled execution-verified.

## Volatile MMIO authority checkpoint

The production/freestanding OS MMIO owner contained thirteen untagged raw
volatile, barrier, and ARM cache declarations, and its wrappers called them
without lexical unsafe authority. The semihost UART path duplicated two more
untagged volatile declarations and three direct calls. All fifteen declarations
are now explicitly `unsafe(ffi)` (and `raw_ptr` where an address is consumed),
and every raw call is confined to the smallest wrapper block.

The eight ordinary OS read/write wrappers and their eight entry-closure aliases
are inline; aliases reuse the owner wrapper instead of adding a second raw-call
site. There is still one provider call per MMIO access and no new allocation,
copy, lookup, lock, generic dispatch, hash, signature check, or retry. The Rust
interpreter's eight `rt_volatile_*` entries now reuse the checked address lift,
rejecting null, negative, host-width-invalid, and misaligned addresses before
volatile access. Native target providers remain deliberately unsafe and
unsigned because target mapping/device ownership cannot be established from an
integer address.

Both touched Simple modules passed the available checker, but it identified
itself as the Rust bootstrap seed. Optimizer O3 analysis found only MIR findings
and no allocation/general pattern. A focused static ratchet passes. The Rust
unit test remains blocked by the already-recorded runtime export drift, and
whole-file `rustfmt --check` is blocked by unrelated existing formatting drift;
neither provider family is promoted to verified or signed-admitted.

## Checked dynload and typed boolean checkpoint

Current Pure Simple wrappers already declared status/out load and symbol APIs,
but the C, Rust-runtime, interpreter, and codegen providers were absent after
tree drift. Raw interpreter load/symbol failure also returned integer zero, and
the generic integer bridge accepted `bool` by coercing it to 0/1. That combined
missing provider and fabricated-value state is now removed.

`spl_dlopen_checked`, `spl_dlsym_checked`, and
`spl_dlsym_process_checked` now initialize output to zero and return distinct
invalid-contract/load-failure/missing-symbol statuses across both C owners,
the Rust runtime, and the interpreter. Interior-NUL paths/names and null handles
fail before platform lookup. Legacy native scalar entry points remain unsafe
compatibility shims, while the safe loader routes through status/out.

Boolean calls no longer cross the integer ABI. Allocation-free typed
`bool()` and `bool(i64)` status/out thunks exist in C, Rust runtime, interpreter,
dispatch, and codegen lanes. They initialize false before validation, preserve
real false/true, and distinguish null function/output failures. The C harness
passes ten cases, including legitimate integer zero and all boolean outcomes.

Exact Linux admission also restores the sealed memfd snapshot provider. Its
sabotage check proves the snapshot is write-sealed and loads the originally
hashed bytes after pathname replacement. Load/path copies happen once during
admission; boolean hot thunks allocate nothing and call the cached function
pointer directly. The older checked integer bridge still allocates a two-value
result array per call and remains a separately tracked performance migration.
## TCP/UDP cross-lane scalar ABI checkpoint (2026-08-26)

The refreshed owned-boundary census reports 13,009 SFFI declaration rows and
11,352 `rt_` rows.  Of the `rt_` rows, 2,826 are explicitly unsafe-tagged,
8,277 are untouched by the unsafe/contract/evidence migration, and zero are
cryptographically admitted.  At symbol granularity there are 3,033 distinct
`rt_` names: 1,433 have every declaration unsafe-tagged, 1,600 have incomplete
tagging, 1,046 are untouched, and zero are admitted.  Provider provenance is
mixed across C, C++, Rust exports, Rust interpreter implementations, system C,
external C ABI, freestanding code, and 1,165 rows with no observed provider;
the inventory does not mistake a language label for ABI or signature proof.

Review of the network guard found a real C/Rust/Simple mismatch.  Rust and the
canonical Simple declarations used scalar booleans for TCP/UDP status while
the AOT C provider and codegen registry retained `int64_t`/I64 in the TCP
family.  The C provider, header, and Cranelift registry now use `bool`/I8 for
bind/listen, close/flush/shutdown, option setters, and UDP status operations.
The interpreter rejects invalid family tags rather than selecting IPv4.  The
C timeout connector now performs one nonblocking connect, `poll(POLLOUT)`, and
`SO_ERROR` validation instead of ignoring the budget and blocking.

Unsupported TCP reads and address queries now return the runtime nil sentinel;
unsupported writes return `-1`, so platform absence cannot look like a valid
empty transfer.  A failed hosted C read frees its already-created buffer and
returns nil, while EOF remains a valid empty byte array.  No successful read
allocation was added.

Optimized object comparison against the exact pre-change tree showed scalar
hot leaves shrinking (`close` -5 bytes, `set_nonblocking` -6,
`set_nodelay` -13), with UDP connect/close unchanged.  `tcp_read` grew 44 bytes
for validation and failure cleanup; both versions contain the same one
successful-path array allocation, and the new version adds only failure-path
release.  No malloc family, dynload, symbol lookup, map, lock, or generic
dispatch was introduced.

This checkpoint is unsafe-minimization and cross-lane source verification, not
signed admission.  The global guard now clears network failures and remains
red only for checked ECDSA facade ownership and raw SSH verification imports.

## Canonical checked-crypto ownership checkpoint (2026-08-26)

The last ECDSA findings were checker drift: the common P-256 module already
imports safe `Result` wrappers from the canonical `signature_sffi` owner and
correctly contains no raw runtime declaration.  The guard now requires that
safe import, requires raw checked declarations only in the canonical owner,
and rejects checked or legacy raw ECDSA externs in the common layer.  The SSH
session also carried an unused raw RSA verifier declaration; it was removed
rather than annotated.

The improved guard passes.  The post-change census reports 13,007 SFFI rows,
11,350 `rt_` rows, and 3,032 distinct `rt_` symbols.  There are 2,825 tagged
`rt_` rows, 8,276 untouched rows, 1,599 symbols with incomplete unsafe tagging,
1,045 untouched symbols, and zero signed-admitted declarations or symbols.
The lower tagged count reflects deletion of a duplicate tagged declaration,
not reduced confinement.

The SSH module check passes.  Optimizer analysis reports no change requirement
caused by the deleted declaration; its broader suggestions concern pre-existing
MIR/loop/length opportunities in the large session module.  This change adds no
instruction, branch, allocation, copy, lookup, lock, or dispatch to a crypto
hot path because it removes an unused declaration only.

## Providerless async ABI removal checkpoint (2026-08-26)

`src/lib/nogc_async_mut/async/sffi.spl` declared 19 generic Future, Promise,
task, combinator, and async-I/O externs, but repository searches found no
provider and no imports of that module.  Three names were nevertheless allowed
by the native linker as zero-return stubs, so an absent provider could become a
fabricated result.

The unused declaration module and those three stub permissions are removed.
The canonical Future, Promise, and AsyncIO implementations remain pure Simple.
An executable authority audit prevents the providerless module/imports and
zero stubs from returning while confirming that the canonical owners contain
no raw replacement externs.  Their source checks pass, and the existing async
basics spec passes 25/25.

This removal adds no runtime instruction, branch, allocation, copy, lookup, or
dispatch.  It reduces the total SFFI declaration inventory by 19 without
changing the `rt_` inventory.  It is unsafe-surface reduction, not signed
provider admission.

## Generic interpreter FFI removal checkpoint (2026-08-26)

The backing-aware census found 14 declarations in
`src/app/interpreter/ffi/extern.spl`: five providerless `call_ffi_0..4`
trampolines, duplicated platform dynload declarations, and Windows loader
declarations.  Repository references prove the lane was reachable only from
two private, unused helpers in `bridge.spl`; no caller used those helpers or
the exported loader facade.

The lane erased every signature into an integer call ABI, converted `nil` to
zero, packed typed arguments into `u64`, returned pointers as integers, and
allocated argument/byte arrays.  It is deleted rather than annotated.  The
typed native registry remains, and an executable guard prevents the generic
dispatcher or its loader facade from returning.

The guard passes and the package initializer checks successfully.  Direct
checking of the surviving bridge is blocked by pre-existing Rust-like syntax
at the unchanged beginning of the file; the exact blocker is recorded under
`doc/08_tracking/bug/`.  Optimizer analysis reports only low-confidence MIR
opportunities.  Removing dead code adds no hot-path work and eliminates any
possible generic marshalling allocation or dispatch.

The requested lint lane was also attempted once and failed in the compiler,
before producing a file verdict, because `Linter.lint_source_for_parsed_append`
is unresolved.  This is the already-recorded lint-subsystem clobber blocker in
`stale_snapshot_clobber_4edef8fab8e_2026-08-26.md`, not a green lint result.

## Providerless QUIC ABI removal checkpoint (2026-08-26)

The native-quiche facade declared 14 `rt_quic_*` functions without any C or
Rust provider.  Its provider authority is deliberately constant
`Unavailable`, so all raw calls were unreachable, while two mirrored unit
specs repeated the same 14 unresolved declarations.  The source tree therefore
carried 42 raw QUIC declarations for a provider that cannot be admitted.

The raw module and test-local extern shadows are removed.  The connection API
is now an explicit pure-Simple terminal-state compatibility facade: constructors
return closed connections, writes/timers return the existing failure sentinel,
and no native lookup or call exists.  A future native provider must introduce a
typed reviewed contract rather than changing the availability enum alone.

The QUIC authority audit and source check pass; the pure compatibility spec
passes 12/12.  Optimizer analysis reports no opportunity.  Every retained leaf
remains O(1), and removing unreachable provider checks/calls reduces branches
and code without adding allocation, copying, lookup, or dispatch.  The refreshed
repository census is 12,929 total declarations and 11,305 `rt_` declarations,
with zero signed admission; exactly 42 `rt_quic_*` declarations are removed by
this tranche, while concurrent upstream census movement accounts for the other
three-row difference from the preceding checkpoint.

## Dead executable-memory generator spec removal (2026-08-26)

The SFFI generator's `exec_memory.spl` declared 16 raw allocation, protection,
function-pointer call, and statistics functions.  Every symbol occurred only in
that file: there is no generated Rust target, provider, consumer, or referenced
test.  Its own text also proposed development-time RWX pages despite documenting
W^X as the production requirement.

The dead spec is deleted.  Real loader execution remains owned by
`compiler/99.loader/smf_mmap_native.spl`, which allocates through the existing
mapping primitive and changes pages to `PROT_READ | PROT_EXEC`; Rust loader
memory remains owned by `ExecutableMemory`.  The new authority audit verifies
both the absence of the dead ABI and the presence of the canonical W^X owner.

This is a source-only deletion: it changes no runtime instruction, allocation,
copy, lookup, or dispatch, and it cannot regress a hot path.  The audit passes.
After rebasing concurrent upstream changes, the current source census is 12,910
total declarations, 11,286 `rt_` declarations, and zero signed admission; this
tranche itself removes exactly 16 rows.

The first push gate correctly rejected stale interpreter-gap ledger entries for
all 16 removed symbols.  Their seed, interpreter-gap, unbacked, and raw-unsafe
baseline rows are now deleted, and the focused interpreter-gap scan passes with
238 compiler symbols, zero new, and zero stale.  Broader seed/unbacked/raw
ratchets remain red from large unrelated concurrent baseline drift; those
findings were not rewritten or absorbed into this tranche.

## Live executable-memory provider checkpoint (2026-08-26)

Both Simple loader owners already allocate writable, non-executable mappings
and explicitly transition them to read/execute. The shared native providers
did not enforce that invariant: Unix accepted any host protection mask, Windows
translated an executable allocation request to `PAGE_EXECUTE_READWRITE`, the
core-C bootstrap accepted `0x7`, and the Rust interpreter forwarded RWX to
`mmap`/`mprotect`.

All four provider lanes now reject any protection containing both WRITE and
EXEC before invoking the OS. Windows maps only the admitted NONE, R, W/RW, X,
and RX forms and no longer references `PAGE_EXECUTE_READWRITE`. The legacy
unmap owner also rejects null or non-positive extents before signed-to-size
conversion. A Rust sabotage test covers both direct RWX allocation and an
RW-to-RWX transition.

The provider audit passes in 0.07 seconds at 2,560 KiB peak RSS. Normal RW and
RX operations retain one syscall and no allocation, copy, lookup, or new
dispatch; the only added work is a constant-time mask comparison before a
mapping/protection syscall. This hardens W^X but does not establish
instruction-cache synchronization on non-coherent architectures, exact-artifact
signature admission, or whole-SFFI verification.

Focused Unix provider syntax and core-C bootstrap syntax (with the build's GNU
feature set) pass. The focused Rust sabotage test cannot compile because the
current workspace is independently missing `read_trace`, import-performance
counters/lowerer fields, UDP/TLS interpreter exports, and atomic-bool exports;
none of the emitted diagnostics points at the mmap change. This checkpoint is
therefore C/provider-audit verified but not a green Rust execution result.

### Cache-coherence follow-up

The no-op `native_flush_icache` API is now a compatibility fence: its existing
RX transition performs the real synchronization. Unix native providers use
`__builtin___clear_cache` after successful executable protection on non-x86
targets and revoke the mapping to `PROT_NONE` if synchronization is unavailable.
Windows calls `FlushInstructionCache` and restores the previous protection on
failure. The core-C bootstrap mirrors both policies. The Rust interpreter has
no independently verified non-x86 primitive, so it rejects executable
transitions before `mprotect` on those hosts rather than executing stale code.

The same provider audit remains 0.07 seconds and 2,560 KiB peak RSS. Optimized
x86-64 assembly contains one `mprotect` call and no cache helper call; the
coherent-architecture branch is eliminated. Unix, GNU core-C, and MinGW syntax
checks pass. No SFFI symbol, per-call lookup, allocation, copy, or new Simple
dispatch was added. The Rust interpreter is safe-by-rejection on hosted ARM/
RISC-V, not feature-complete there, and exact-artifact signing remains absent.

## Signed-admission receipt join repair (2026-08-26)

The cryptographic admission verifier successfully checked hashes, the
provider-scoped Ed25519 trust root, and the manifest signature, but emitted a
flat five-column table. Both census consumers immediately searched that output
for a unique `provider_id`, while the canonical Simple parser expected
`simple.sffi-admission.v1` framing. Therefore every configured admission job
failed after cryptographic verification and could never become `reverified`.

The verifier now emits the canonical framed receipt: provider, target, signer,
artifact/ABI/signed-manifest/report digests, symbol count, and sorted verified
symbol rows. The contract test now feeds that receipt through the real
`SFFI_ADMISSION_JOBS` inventory join using an owned `@sffi(provider: ...)`
declaration and exact source-signature hash. It passes, as do tampered artifact,
stale/failed report, untrusted/duplicate key, noncanonical manifest, and
substituted-signature rejection controls.

This is admission-time tooling only; it changes no provider call path. The
expanded fixture completes in 1.5 seconds. It deliberately generates ephemeral
test trust material and does not count as production signed admission. A real
external trust policy and exact production build inputs are still required, so
the repository-wide signed-admitted count remains zero.

## Providerless debug command-output removal (2026-08-26)

The backing-aware census found four production declarations of
`rt_command_output`, ten scoped call sites, and no C, Rust, interpreter, or
native provider. The raw function returned only `text`, so command-not-found,
nonzero exit, stderr-only failure, and legitimate empty stdout could not be
distinguished.

All four declarations are removed. A single pure-Simple compatibility module
now calls the existing typed `process_run_bounded` facade with a 120-second
timeout and 1 MiB output bound. Its argv path and fixed-script/positional-arg
shell path both return `Result<text, text>`, preserve stdout only on exit zero,
and map nonzero exit plus bounded stderr to `Err`. Untrusted device paths,
serials, filenames, commands, and ports are argv/positional data rather than
interpolated shell syntax. Callers either propagate the error or deliberately
reduce probe failure to their existing `unknown` adapter result.

The helper retains one child process and O(output) capture. It adds no foreign
lookup, generic dispatch, retry, second child, or per-byte loop. The new spec
passes 3/3 under the available Rust bootstrap runner in 6.84 seconds with
176,820 KiB peak RSS, including a literal shell-substitution sabotage value,
so this is compatibility evidence, not a pure-Simple
Stage-4 claim. All five touched sources pass `check`; the authority and
direct-runtime guards pass; optimizer analysis reports only low-confidence
bounds/dead-code opportunities for the helper and no allocation/copy/loop/
dispatch finding. Lint was attempted once but all five invocations stop at the
pre-existing `Linter.lint_source_for_parsed_append` code-generation gap (exit
70), tracked in
`doc/08_tracking/bug/stale_snapshot_clobber_4edef8fab8e_2026-08-26.md`; no lint
PASS is claimed.

The post-change source census is 12,888 total declarations, 11,264 `rt_`
declarations, 2,986 distinct `rt_` symbols, 1,553 symbols with incomplete
unsafe tagging, 1,002 untouched `rt_` symbols, and zero signed-admitted rows or
symbols. This removes exactly four declaration rows and one providerless
symbol. It does not verify or sign the canonical process provider or wider
SFFI estate.

### Unimplemented interpreter debug hooks are unsafe capability gaps (2026-08-26)

The `rt_hook_*` family has 14 distinct symbols and 42 declarations across the
sync DAP library, async DAP mirror, and SFFI-generator specification. The
backing-aware inventory finds no C, Rust, interpreter, or native provider.
Every declaration is now explicitly `unsafe(ffi)`, and the Rust interpreter
maps an unresolved `rt_hook_*` call to the existing typed capability-gap error
rather than a generic unresolved-extern value. The focused source census is
42/42 unsafe-tagged rows, 14/14 completely tagged symbols, and zero signed
admissions. The targeted Rust unit test passes 3/3; the installed compatibility
runner predates this Rust dispatch and is therefore not counted as verification.

This is classification and fail-closed error routing, not a provider
implementation, nullability proof, cryptographic admission, or full lexical
call-site proof. It changes only the unknown-extern error path: normal provider
dispatch, allocation, copying, and hot-call complexity are unchanged.

### Owned SimpleOS C providers in the backing census (2026-08-26)

The backing census previously scanned C/C++ only below `src/runtime`, although
the owned SimpleOS runtime also exports `rt_*` providers below `src/os`. That
made real target-gated C functions such as `rt_mem_read_u8`, `rt_pci_get_field`,
and `rt_net_init` appear genuinely missing. The source scanner now covers both
owned roots while retaining vendor exclusion. It reclassifies 68 symbols as
`c_runtime_source_only`; the published unbacked baseline deliberately removes
the 60 affected unbacked entries.

This corrects inventory provenance only. `c_runtime_source_only` means source
evidence exists but the deployed host binary, ABI contract, safety proof, and
signature admission are still absent. The one-shot shell audit has no compiled
runtime hot path, allocations, or dispatch change. The global unbacked ratchet
is currently blocked by concurrent baseline drift (46 new and 370 stale rows),
which is recorded rather than silently regenerated.

### HDA PCI raw boundary confinement (2026-08-26)

The HDA PCI binding declared four raw scalar functions. Two are present only in
the native test stub, and the field-number convention differs from the
RISC-V-only PCI source provider, so neither source presence nor the test stub
is a portable ABI proof. Replacing it with the general Pure-Simple `PciBus`
would add a full-bus scan and dynamic device-array allocation to audio boot;
that is rejected as a performance/memory regression.

All four declarations now carry explicit `unsafe(ffi)` authority and all raw
calls pass through four `@always_inline` lexical owners. This preserves the
existing scalar call shape—no new loop, allocation, copy, lookup, or dynamic
dispatch—and makes target/provider uncertainty visible. Source check and the
authority audit pass. The native-stub spec cannot execute under the available
bootstrap runner because `rt_hda_pci_probe_set_mode` is unregistered; this is a
runtime-evidence blocker, not a pass. No provider is signed or verified.

### Debug ptrace/DWARF declaration consolidation (2026-08-26)

Four debug frontend/mirror modules redeclared the same ptrace and DWARF raw
ABIs that already have the canonical `std.sffi.debug` owner. They now import
that owner, removing 46 duplicate raw declaration rows without adding a call,
allocation, copy, lookup, or dispatch. The new authority audit prevents the
duplicates from returning; all four modules pass source checking and optimizer
analysis reports only pre-existing local opportunities.

This reduces unsafe surface duplication, not the remaining unsafe contract:
ptrace memory/register containers and DWARF strings/arrays have no verified
ownership/nullability/provider-admission evidence, and the family remains
unsigned and critical-ineligible.

### Providerless legacy CUDA-session removal (2026-08-26)

The legacy no-GC engine2d `CudaComputeSession` had nine raw CUDA declarations
with no provider, including signatures incompatible with the canonical typed
CUDA owner. It had no production import; its only consumer exercised bounded
module-cache bookkeeping. The execution façade is removed rather than mapping
foreign failure to `0`, `false`, or empty text. The module now contains only
the four-slot pure cache and rejection accounting used by that contract.

The cache spec passes 2/2 before and after the change, source check passes,
and the providerless guard confirms no raw CUDA extern/call can return. The
flat four-slot layout, O(1) lookup, and allocation behavior are unchanged;
the deleted SFFI call paths reduce code and runtime risk. This does not verify
or sign the still-active typed CUDA providers.

### Serial owner consolidation and inventory repair (2026-08-26)

The prior serial estate had three raw declaration owners.  The app and
bare-metal copies used `i32` widths that disagreed with the canonical `i64`
runtime ABI; they also exposed baud/parity/data-bit/stop-bit/availability calls
for which no admitted provider was observed.  The unused app copy is removed.
`std.nogc_sync_mut.io.serial_sffi` is the one raw owner, with seven explicit
`unsafe(ffi)` declarations.  The dedicated-hardware transport uses its typed
`SerialPort` façade, so it no longer redeclares or directly invokes raw serial
symbols.  The unsupported availability request now returns a typed `Err`
without issuing a foreign call.

This preserves the serial I/O complexity: one façade call remains per physical
I/O operation; no polling loop, buffer copy, lookup, or allocation was added.
The inventory tool's default stdout mode also now spools the TSV privately
before aggregation, fixing its former self-pipe hang.  Neither change signs or
verifies the runtime serial provider; it remains unsafe, unsigned, and
unverified.

### Providerless legacy WebGPU-session removal (2026-08-26)

The legacy `WebGpuSession` declared eleven `rt_wgpu_*` functions for an
instance/adapter/device execution chain. No C, C++, or Rust provider was found,
and no production import exists; its sole consumer tests the four-slot shader
cache. The execution façade is removed rather than leaving handles and text
results vulnerable to a missing-provider fallback. The retained module is pure
bounded cache/rejection accounting. A second unused duplicate owner,
`webgpu_ffi.spl`, is also removed.

The active `webgpu_sffi` rendering boundary remains because production backends
use it; its eleven declarations are now explicit `unsafe(ffi)`. The direct call
shape and buffer behavior are unchanged. Source checks, pure cache spec, owner
audit, and optimizer analysis pass. This is not ABI, null/ownership, artifact,
or signature verification of the active WebGPU provider.

### Providerless legacy Metal-session removal (2026-08-26)

The no-GC `MetalComputeSession` declared ten `rt_engine2d_metal_session_*`
functions, but no owned C/C++/Rust provider or production import was found.
Those declarations are removed rather than allowing a missing provider to be
represented as a handle or text value.  The distinct active GC Metal backend is
unchanged; it remains an unsafe, unsigned, unverified SFFI owner.

The retained no-GC module is only its fixed four-slot, allocation-free pipeline
cache and rejection accounting.  Its existing two-example cache spec passes,
the providerless guard prevents raw declarations/calls from returning, and the
optimizer reports only existing local dead-code observations.  This deletes a
dead unsafe execution surface without adding a loop, allocation, copy, lookup,
or dispatch to the cache path.

### Intel Engine2D raw-owner consolidation (2026-08-26)

The active GC Intel Engine2D kernel helper redeclared eleven raw
`rt_intel_engine2d_*` functions even though the no-GC Intel SFFI owner already
provided matching wrappers. The backend now imports those wrappers under its
existing local helper names, preserving one direct call at each argument-set
or upload/download site. No loop, allocation, copy, lookup, or extra dispatch
is introduced to the render path.

Both retained raw Intel declaration surfaces (`sffi_intel` and compatibility
`ffi_intel`) now mark all 21 declarations `unsafe(ffi)`. The owner audit
confirms 42 tagged raw declaration rows and none in the active GC consumer.
This records the still-unverified Level Zero/Engine2D ABI boundary; it does not
prove pointer/array layout, nullability, ownership, artifact identity, or a
signature-admitted provider.

### OpenCL raw-owner classification (2026-08-26)

The OpenCL ICD has one active raw owner and a real owned C implementation, but
source presence is not ABI/nullability/ownership proof or signed admission.
All 20 `rt_opencl_*` declarations are now explicitly `unsafe(ffi)`, and an
authority audit rejects a second raw declaration owner. The existing eight-case
spec exercises fail-closed invalid-handle and name-only-kernel behavior.

This is metadata and audit work only: it adds no render-path branch, lookup,
allocation, copy, or dispatch. Optimizer analysis reports no general-pattern
finding. The provider remains unsigned and unverified.

### ROCm Engine2D raw-boundary classification (2026-08-26)

ROCm has an already-explicit no-GC I/O SFFI owner, but two older public
Engine2D dispatch façades retain 12 and 13 raw declarations respectively.
They are still active compatibility surfaces, so removing them would change
backend behavior. All 25 raw declarations now carry `unsafe(ffi)` (and
`raw_ptr` where their handle/array ABI requires it); the authority audit keeps
that classification from regressing.

The existing 13-case ROCm spec passes, including the fail-closed legacy
kernel-path cases. This metadata-only change adds no draw-path branch,
allocation, copy, lookup, or dispatch. It does not establish typed span/handle
contracts, target hardware behavior, artifact identity, or signed admission.

### 3D GPU raw-owner deduplication (2026-08-26)

CUDA, ROCm, Intel, and Vulkan each had an `ffi_*3d` raw module that duplicated
its corresponding `sffi_*3d` module byte-for-byte. The former now preserves its
public module path as a compatibility re-export; only the four canonical
`sffi_*3d` modules retain raw declarations. Their twelve declarations are
explicitly `unsafe(ffi)` and a source audit enforces the one-owner rule.

This removes twelve declarations and duplicate class implementations without
adding a render-path branch, allocation, copy, lookup, or dispatch. All eight
modules source-check, and optimizer analysis reports no general-pattern finding
for the four canonical owners. The provider identities remain unverified and
unsigned.

### OpenGL raw-boundary classification (2026-08-26)

The active OpenGL owner is `std.nogc_sync_mut.io.opengl_sffi`; every one of
its nineteen raw declarations now explicitly requires `unsafe(ffi)`, and every
wrapper contains the lexical unsafe boundary at the direct call. The public
API stays boolean for operations whose provider ABI is boolean; this does not
substitute numeric truth values. The one error-text ABI that may return no
provider message is now `text?`, so nil is represented explicitly rather than
as a non-null text value.

The source authority guard confirms a single raw owner. The source check and
existing OpenGL fallback spec pass. This is annotation/return-shape work only:
no render-loop allocation, copy, lookup, dispatch, or retry was added, and the
optimizer found no general source-pattern regression. The OpenGL provider is
still unsafe, unsigned, and unverified; these changes do not prove buffer
extent, handle ownership, ABI identity, or artifact admission.

### File-operations raw-boundary classification (2026-08-26)

The shared no-GC `file_ops` owner retains nineteen required raw filesystem and
mmap hooks. Every declaration is now explicit `unsafe(ffi)` (with `raw_ptr`
for mapping address/extent operations), and every direct call is lexical-unsafe.
This is a containment step, not a safe-wrapper claim: legacy mmap/hash text
declarations still need a typed nullable/result migration.

The file-ops authority guard and four-module source check pass. The optimizer
finds no general source-pattern change, and the edit adds no loop, allocation,
copy, lookup, retry, or dispatch to any file hot path. The nominal integration
spec is blocked because its selected bootstrap artifact predates the existing
source registration for `rt_file_read_regular_no_follow_bounded`; a concrete
bug record captures the deployment-parity reproduction rather than asking for
a stub.
