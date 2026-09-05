# Blocking Infrastructure Interfaces for Aspect Dynload

**Date:** 2026-08-19
**Scope:** the six sections of
`doc/05_design/language/aop/aspect_facet_dynload_smf_pack_design_2026-08-04.md`
that cannot be implemented today because the layer beneath them is absent.
**Purpose:** define the MINIMAL interface for each, so those sections become
implementable — and, where an interface would be a fake gate, say so instead of
designing decoration.

## 0. Verdict table (the most important output)

| # | Section | Verdict | Rests on |
|---|---|---|---|
| 1 | §15 Mapping and I/O policy | **INTERFACE-ONLY** — build now | `rt_mmap_raw`/`rt_madvise_raw`/`rt_open_fd`/`rt_page_size` already exist |
| 2 | §14.1 `AspectPackIndexCache` | **INTERFACE-ONLY** — build now, on top of #1 | `aspect_pack.spl` parsers + #1 |
| 3 | §14.1 `AdviceBindingRegistry` | **NEW INFRASTRUCTURE — do NOT build yet** | needs backend join-point patchpoints, which do not exist at all |
| 4 | §14.2 Runtime state machine | **INTERFACE-ONLY (partial)** — buildable as a pure state table; the transitions it drives are not | #2 for the early states, #3/#6 for the late ones |
| 5 | §14.6 Concurrency | **NEW INFRASTRUCTURE (small)** — a real CAS/once-cell must be proven first | `nogc_async_mut/atomic.spl` is a 13-line re-export shim, not a verified primitive |
| 6 | E-APACK003 signature verification | **DO NOT BUILD — fake gate today** | `pure_ed25519_verify` exists; the *trust anchor* does not |

**Honest split: 2 of the 6 should not be built now (#3, #6), 1 should not be
built before a prerequisite is proven (#5), 2 are buildable today (#1, #2), and
1 is half-buildable (#4).**

---

## 1. §15 Mapping and I/O policy — INTERFACE-ONLY

### What already exists
- `src/compiler/99.loader/loader/smf_mmap_native.spl` — `rt_mmap_raw`,
  `rt_munmap_raw`, `rt_madvise_raw`, `rt_open_fd`, `rt_close_fd`,
  `rt_page_size`, `native_mmap_read_bytes` (byte reads off a mapped address).
- `src/lib/nogc_sync_mut/io/file_ops.spl` — `file_size`, `file_read_text_at`
  (offset read, TEXT only), `file_mmap`/`file_madvise` (whole-file oriented).
- `src/compiler/99.loader/loader/smf_cache.spl` — the WHOLE-FILE + `SEQUENTIAL`
  policy §15 explicitly says is wrong for cold packs.

### What is missing (and it is small)
`native_mmap_file` passes the caller's `offset` straight to `mmap(2)` with **no
page alignment**. `mmap` rejects an unaligned offset with `EINVAL`, so there is
today no way to map "just the trailer" or "just the directory" of a pack — the
only working call is offset 0. That single gap is what blocks §15.

There is no byte-oriented `pread`: `rt_file_read_text_at` returns `text`, which
is lossy for binary pack bytes. Rather than add a new extern, the window mapper
below covers the same need (map an aligned window, read bytes out of it, unmap).

### Interface

Module: **new** `src/compiler/99.loader/aspect_pack_io.spl`
(NOT in `smf_mmap_native.spl` / `object_mapper.spl` — those are whole-file SMF
policy and must keep their `SEQUENTIAL` behaviour unchanged).

```simple
struct PackWindow:          # an aligned mapping that covers [want_offset, +want_length)
    address: i64            # page-aligned mapping base, 0 = failed
    map_length: i64         # aligned length actually passed to mmap
    data_offset: i64        # want_offset - aligned_base; add to address-relative reads
    want_length: i64
    ok: bool
    error: text

fn pack_window_map(path: text, want_offset: i64, want_length: i64) -> PackWindow
fn pack_window_bytes(w: PackWindow) -> [u8]         # exactly want_length bytes
fn pack_window_unmap(w: PackWindow) -> bool
fn pack_window_willneed(w: PackWindow) -> bool      # MADV_WILLNEED, explicit opt-in only
fn pack_read_range(path: text, offset: i64, length: i64) -> [u8]  # map+read+unmap, the pread stand-in
fn pack_read_trailer(path: text, trailer_size: i64) -> [u8]       # tail read without knowing the layout
```

Policy rules the interface enforces, not merely documents:
- No `MADV_SEQUENTIAL` is ever issued. Readahead is opt-in via
  `pack_window_willneed` only (§15: "Issue WILLNEED only for explicit
  startup/preload closures").
- `want_offset + want_length` is bounded by `file_size(path)`; an out-of-range
  request fails closed rather than mapping a short region.

### What it does NOT cover
Writing; shared/`MAP_SHARED` mappings; executable mappings (that stays in
`smf_mmap_native.spl`); cross-process cache coherency; Windows. It is a
read-only range reader, nothing more.

### The one test that proves it real
Map a range whose offset is deliberately **not** page-aligned (e.g. a directory
starting at byte 4101 of a >2-page file) and assert the returned bytes equal the
same slice of a whole-file read. That single assertion is the entire difference
between this module and the existing one — a naive implementation returns
`EINVAL`/empty and fails.

---

## 2. §14.1 AspectPackIndexCache — INTERFACE-ONLY (on top of #1)

### What already exists
`src/lib/common/aspect_pack.spl` already parses the pack header/directory and
loads a module (`apk_open_pack_v1`, `apk_load_module_v1`), and already carries
the declared-uncompressed-size bound (`APK_MAX_MODULE_UNCOMPRESSED_SIZE`,
checked *before* inflating). It takes `data: [u8]` — the WHOLE FILE in memory.
That is precisely the policy §15 forbids for cold packs.

So the cache needs **no new parsing and no new decompression** — it needs a
file-backed front door that feeds those parsers only the trailer and directory.

### Interface

Module: **new** `src/compiler/99.loader/aspect_pack_index_cache.spl`.

```simple
struct PackIndexEntry:
    pack_path: text
    file_size: i64
    mtime: i64              # file_stat() — cheap staleness key
    index_bytes: [u8]       # header + directory only, never payload
    module_count: i64
    ok: bool
    error: text

struct PackIndexCache:
    entries: Dict<text, PackIndexEntry>
    hits: i64
    misses: i64
    index_bytes_read: i64   # must stay << sum of file sizes; this is the proof metric

fn pack_index_cache_new() -> PackIndexCache
fn pack_index_get(c: PackIndexCache, pack_path: text) -> PackIndexEntry
fn pack_index_invalidate(c: PackIndexCache, pack_path: text) -> bool
fn pack_index_evict_all(c: PackIndexCache) -> i64
```

Entry is invalid when `(file_size, mtime)` differs from what was recorded —
same staleness discipline `smf_cache.spl` uses, no new mechanism.

### What it does NOT cover
Payload chunks (§14.1: "does not imply loading payload chunks"); the
decompressed-module content-hash cache (a separate, later cache); cold-debug-
chunk eviction; concurrent access (single-threaded until #5 lands).

### The one test that proves it real
Build a pack with one small and one large module, then assert
`index_bytes_read < file_size` after a `pack_index_get` — i.e. the cache
demonstrably did **not** read the payload. A whole-file implementation makes
that assertion fail.

---

## 3. §14.1 AdviceBindingRegistry — NEW INFRASTRUCTURE, DO NOT BUILD YET

`/usr/bin/grep -rn "patchpoint\|patch_point\|join_point_slot" src/compiler
src/runtime` returns **zero** hits. §14.1 says the registry "maps prepared
join-point slots to static, startup, or dynamic advice chains" — there are no
prepared slots. The backend emits no reserved call sites, no relocation records
naming them, and no per-slot indirection word to publish into.

A registry built now would be a `Dict<text, [text]>` that nothing consumes: it
could be populated and queried and would still change no program's behaviour.
That is decoration, not a gate.

**Prerequisite, stated so it can be scheduled:** codegen must emit, per
join-point, (a) an indirect dispatch word in a writable section, (b) a stable
slot ID in SHB metadata, and (c) a relocation entry so the loader can find the
word. Only then does a binding registry have an addressable target. That is a
backend change in `src/compiler/70.backend`, not an interface.

Deferred design note: when it exists, the registry's key is
`(slot_id, aspect_generation)` and its value an ordered advice chain, published
by generation swap (§14.7 pins generations), so the shape is known — only the
substrate is missing.

---

## 4. §14.2 Runtime state machine — HALF BUILDABLE

The state table itself (`Excluded → Catalogued → IndexMapped → Resolving →
ChunksLoaded → Relocated → Bound → Active → Quiescing → Unloaded`, plus
`Failed`) is pure data and needs nothing. It can be written today as a
transition-validity function with a stable diagnostic per illegal edge.

But the states past `ChunksLoaded` are driven by relocation (existing loader),
binding (#3, absent), and quiescing (#5, unproven). Implementing the machine now
buys a validator for edges nobody can yet traverse.

**Recommendation:** build it *with* #2, limited to
`Excluded → Catalogued → IndexMapped → Failed`, with the later states declared
and their entry functions absent rather than stubbed-true. A stub that returns
`Active` unconditionally is worse than a missing function.

Interface sketch (for when it lands): `struct AspectState` (enum-like i64 +
diagnostic text), `fn aspect_state_can_transition(from, to) -> bool`,
`fn aspect_state_fail(state, code, message) -> AspectState`. Belongs in
`src/compiler/99.loader/`. Test that proves it: an illegal edge
(`Catalogued → Bound`) must be rejected with its stable code, not silently
allowed.

---

## 5. §14.6 Concurrency — NEW INFRASTRUCTURE (small), PROVE THE PRIMITIVE FIRST

§14.6 needs exactly two things: a **single activation future per aspect
generation** (concurrent callers wait rather than duplicate the load) and a
**dependency stack that rejects cycles before publication**.

The cycle stack is trivially buildable today — it is a `[text]` with a
membership check, no concurrency required, and it is worth building alongside #2
because it is the half that catches real bugs.

The activation future is not, and the reason is specific:
`src/lib/nogc_async_mut/atomic.spl` is a **13-line re-export shim**, and
`Future<T>` in `src/lib/nogc_sync_mut/src/future.spl` is a struct whose
completion semantics under real threads are unverified here. A "single
activation" that is actually a non-atomic check-then-set is a race that will
duplicate loads under exactly the contention it exists to prevent — a fake gate
with a real cost.

**Prerequisite:** a verified compare-and-swap (a test that spawns N threads,
each CAS-ing a shared word, and asserts exactly one wins). Until that test
exists and passes, do not build the activation future.

Interface, once the primitive is proven:
`fn activation_begin(gen_id: text) -> bool` (true = you own the load, false =
another owns it and you must wait), `fn activation_wait(gen_id: text) ->
ActivationResult`, `fn activation_complete(gen_id, result)`.
Test that proves it: N concurrent `facet<T>()` first-uses on one cold pack must
yield `packs_opened == 1` (the counter already exists in `aspect_pack.spl`).

---

## 6. E-APACK003 signature verification — FAKE GATE, DO NOT BUILD

`src/lib/common/crypto/ed25519.spl` provides `pure_ed25519_sign` and
`pure_ed25519_verify`. The *cryptography* is not the gap.

The gap is that there is **no signing authority in-tree**: no trust anchor, no
root public key with a defined provenance, no key distribution, no revocation,
no policy for who may sign a pack. A verifier built now would check a signature
against a key that ships in the same repository as the packs it verifies —
anyone able to modify a pack is able to modify the key. It would report
`E-APACK003 PASS` on every input an attacker controls. That is strictly worse
than no check, because it produces a green verdict that means nothing.

**Do not build it.** Build the half that is real instead, and name it honestly:

- **Content-hash verification IS real and IS buildable now.** The pack directory
  can carry a hash per chunk; `aspect_pack.spl` already computes CRC
  (`_apk_crc`) and `sha256` is available via `file_hash_sha256`. This catches
  corruption, truncation, and stale caches — everything E-APACK003 covers
  *except* adversarial tampering.
- Report it under a distinct code (e.g. `E-APACK003-HASH`) so nobody later reads
  a hash pass as a signature pass.

**Prerequisite for the real thing:** a documented trust root — where the root key
lives (outside the artifact tree), who holds the private half, and what
revocation looks like. That is an organisational decision, not a module.

---

## 7. Build order implied by the above

1. `aspect_pack_io.spl` (§15) — nothing depends on anything.
2. `aspect_pack_index_cache.spl` (§14.1) — on top of 1.
3. Dependency-cycle stack + the early half of the state machine — cheap, real.
4. *Blocked:* verified CAS → activation future (§14.6).
5. *Blocked:* backend patchpoints → `AdviceBindingRegistry` (§14.1).
6. *Blocked on a decision, not code:* trust root → E-APACK003 signatures.

## References
- `doc/05_design/language/aop/aspect_facet_dynload_smf_pack_design_2026-08-04.md`
- `src/lib/common/aspect_pack.spl`
- `src/compiler/99.loader/loader/smf_mmap_native.spl`, `.../loader/smf_cache.spl`
- `src/lib/nogc_sync_mut/io/file_ops.spl`
- `src/lib/common/crypto/ed25519.spl`

---

## 8. Implementation record (2026-08-19) — what building #1 and #2 actually taught

Items 1 and 2 were built as designed above. Four things the design did not
anticipate, all found by running the specs rather than by reading code, and all
now encoded in the modules:

**8.1 The loader's low-level mmap externs are not callable.**
`rt_open_fd` and `rt_page_size` are *declared* in
`src/compiler/99.loader/loader/smf_mmap_native.spl` but are **not in the
runtime's extern registry at all** — any call fails semantic analysis with
`unknown extern function`. The path-based `rt_mmap`/`rt_munmap`/`rt_madvise`
family is registered for native codegen but **not in the interpreter**, which is
the engine `bin/simple test` runs on. What *is* registered in both is
`rt_io_file_open` / `_seek` / `_read` / `_close` and
`rt_mmap_raw` / `rt_munmap_raw` / `rt_ptr_read_u8`.

Consequence, and it is an improvement: the primary read path is now a **genuine
pread** (open, seek, read, close) with no page-alignment constraint at all,
which is exactly the first option §15 lists. The aligned mmap window is kept as
the second mechanism, and the fd it needs comes from `rt_io_file_open`.

**8.2 §15's WILLNEED half was NOT built, on purpose.** No madvise extern is
registered in the interpreter, so a `pack_window_willneed` could only ever be
asserted to *exist*, never to *do* anything — a fake gate by the standard this
document applies to E-APACK003. There is also no startup/preload closure to
serve yet. The half that *is* enforced is the load-bearing one and is enforced
by construction: `aspect_pack_io.spl` contains no madvise call, so it cannot
issue the whole-file `MADV_SEQUENTIAL` readahead §15 rules out for packs.

**8.3 Alignment granule is 64 KiB, not the host page size**, precisely because
`rt_page_size` is uncallable. 65536 is a multiple of every page size on the
targets here (4 KiB, 16 KiB, 64 KiB), so a 64 KiB-aligned offset is valid
everywhere; the cost is at most 64 KiB of extra mapped virtual address space per
window, never faulted in.

**8.4 `PackIndexCache` had to become a `class`, and this nearly produced a
vacuous spec.** As a `struct` it is a value: `c.hits = c.hits + 1` inside
`pack_index_get` was discarded at return, so after two lookups the counters read
`hits=0, misses=0, index_bytes_read=0`. The assertion `index_bytes_read < fsize`
— the *entire* proof that the cache does not read payload — was therefore
passing as `0 < 264`, vacuously. Making the cache a class fixed the mutation,
and the spec now carries a companion assertion (`index_bytes_read > 0`) whose
only job is to make the vacuous case impossible to reach again.

**8.5 Known gap, not worked around: staleness is size-keyed only.**
`rt_file_stat` in this runtime returns the file **SIZE**, not a modification
time — measured directly: a 264-byte pack reports `stat == 264 == size`. Folding
it into the staleness key would have added a second copy of the same signal
while reading like a stronger check, so it was dropped. Consequence: **a rebuild
producing a pack of exactly the same length is not detected**; callers that
rebuild in place must call `pack_index_invalidate`. Closing this needs a real
mtime extern; it is a runtime gap, recorded here rather than papered over.

### Delivered

| Path | What |
|---|---|
| `src/compiler/99.loader/aspect_pack_io.spl` | §15 pread + aligned mmap window, declared-range bound |
| `src/compiler/99.loader/aspect_pack_index_cache.spl` | §14.1 index cache, header+directory only, declared-directory bound |
| `test/01_unit/compiler/loader/aspect_pack_io_spec.spl` | 6 examples, PASS |
| `test/01_unit/compiler/loader/aspect_pack_declared_size_bound_defect_class_spec.spl` | 5 examples, PASS |

**Mutation proof of the defect-class spec** (the claim that it is load-bearing,
verified rather than asserted): deleting the `APKIDX_MAX_DIRECTORY_BYTES` check
from `pack_index_read` turns the spec from `5 passed, 0 failed` into
`3 passed, 2 failed` — the two examples that pin the cap's specific error code
go red, exactly as the spec header says they must. The check was restored
immediately afterwards.
