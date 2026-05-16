# svllm A2-Packer — Phase 2 Audit Report

**Date:** 2026-04-18
**Analyst:** Claude (Phase 2 of sstack svllm-a2-packer)
**Scope:** Audit A1..A8 gap matrix; confirm/falsify "A1 done, next = A2"; enumerate
dependencies, fixture strategy, and atomic-publish primitives for the Packer CLI.

---

## 1. Gap Matrix (master plan A1..A8 vs. on-disk reality)

| Phase | Name | Plan deliverables | Files on disk today | Status |
|---|---|---|---|---|
| A1 | Model-loader baseline | tensor-pack format, safetensors reader, manifest, weight_utils; failing TDD tests; stubs for packer + service | 9 `.spl` files under `src/lib/gc_async_mut/svllm/` (svllm `__init__`, `model_executor/__init__`, `model_loader/{__init__, weight_utils, tensor_pack, manifest, safetensors, loader}`, `nvfs_client/__init__`) + 3 spec files + `src/app/svllm_pack/main.spl` stub; `doc/05_design/svllm/{svllm_master_plan.md, fs_requests/README.md}`; `doc/05_design/nvfs/svllm_requirements.md` | **done (surface/types)** — all type surfaces fixed and 19/19 tests pass. Five function stubs return `Err(...)` intentionally to pin TDD targets for A2. A1 AC-9 (submodule gitlink) is the only residual wart, tracked in `feedback_submodule_race_parallel_dev.md`. |
| A2 | Packer CLI | `src/app/svllm_pack/` consumes safetensors → tensor-pack | `main.spl` prints help only; all dependency modules are stubs | **missing — this chunk** |
| A3 | Streaming loader + pinned DRAM | `model_loader/streamer.spl`, `gpu/pinned_pool.spl`, concurrent chunk H2D | no `streamer.spl`, no `pinned_pool.spl` | missing |
| A4 | Paged KV cache + paged attention | `core/block_manager`, `worker/cache_engine`, `attention/backends/paged.spl` | none | missing |
| A5 | Scheduler + worker + executor + engine | continuous batching + chunked prefill; ECS business layer | none | missing |
| A6 | HTTP API | `entrypoints/openai/api_server`, async HTTP bridge via monoio | none | missing |
| A7 | Sleep/wake | `engine/llm_engine.sleep(level)` / `wake_up()` | none | missing |
| A8 | LoRA adapter hot-load | `lora/` tree, per-request adapter routing | none | missing |

**Verdict:** The assumption holds. **A1 is complete as a surface/scaffold** (19/19 tests
pass; all types + stubs landed; docs published); **A2 is the correct next chunk**.
Caveat: A1 deliberately left safetensors parsing, manifest parsing, and
`build_tensor_pack` as failing stubs — those lines fall inside the A2 acceptance criteria
(AC-2, AC-3) of this track, not a new bug.

---

## 2. A2 Packer CLI Dependencies

### 2.1 `safetensors.spl` — **stub only**

- Defines `SafetensorsError`, `SafetensorsTensorEntry`, `SafetensorsHeader` types.
- `parse_safetensors_header(bytes: [u8]) -> Result<SafetensorsHeader, SafetensorsError>`
  currently checks only the 8-byte length prefix; unconditionally returns
  `Err(SafetensorsError.MalformedJson)` for everything else.
- **Missing for A2:**
  - Little-endian u64 decoder for header length (stub doesn't even extract it).
  - UTF-8 / JSON parser for the header (`dtype`, `shape`, `data_offsets` per tensor;
    ignore `__metadata__`).
  - Mapping `dtype` string → `weight_utils.Dtype`.
  - Validation: `data_offsets[1] <= total_payload_len`, ascending offsets, non-negative
    shape dims.
- **Note on JSON:** check whether `std.common.json` is usable from GC runtime modules.
  (Likely yes — it's in `src/lib/common/`.) If not, hand-roll a minimal safetensors-header
  parser (no arbitrary JSON nesting beyond the documented schema).

### 2.2 `tensor_pack.spl` — **read-only types**

- Provides `TensorInfo`, `ChunkInfo`, `TensorPack` with `empty()`, `tensor_count()`,
  `chunk_count()`, `find_tensor()`.
- **Zero writer functions.** No `pack_plan()`, no `emit_chunk()`, no `emit_manifest()`.
- **A2 must add** (deliberately; AC-3):
  - Planning: group `TensorInfo` into chunks bounded by
    `preferred_chunk_bytes` (default 2 MiB per A1 stub spec literal), align each tensor
    to `preferred_read_granule` (default 4 KiB if caps unavailable).
  - Digest helper: BLAKE3 or SHA-256 over each chunk; `std.common.crypto` likely has
    sha256 — verify in 3-arch.
  - Writer entry point: `fn write_pack(pack: TensorPack, sources: [(TensorInfo, [u8])], out_root: text) -> Result<(), WriterError>`.

### 2.3 `manifest.spl` — **surface only, both fns stubbed**

- `parse_manifest(sdn_text) -> Err(Malformed)`; `build_tensor_pack(root, m) -> Err(Malformed)`.
- `TensorPackManifest` struct has fields but no tensor/chunk vectors (the parser's target
  model adds them in the full implementation — check whether to extend the struct or add
  sibling types in A2).
- **Missing for A2:**
  - SDN serializer (manifest → text). SDN is project canonical; see `.claude/rules/language.md`.
  - SDN parser round-trips. A2 writer only needs **serialize**; A3 loader will exercise parse.

### 2.4 `nvfs_client/__init__.spl` — **trait + types only; no implementation**

- Defines `NvfsClient` trait with 11 methods, plus `ObjClass`, `ObjHandle`, `BufHandle`,
  `NvfsCaps`, `CreateFlags`, `SyncScope`, `NvfsError`.
- **No concrete adapter** exists — neither FAT32 nor std.fs-backed. The CLI as written
  today cannot call anything.
- **A2 minimum:** introduce one concrete backing strategy. Two viable options:
  1. **A2-small:** `StdFsNvfsClient` (or rename to avoid confusion) — implements a narrow
     subset (`create`, `write_range`, `close`, `seal` as "rename .tmp → final",
     `publish_atomic` as two-step rename, `query_caps` returning hard-coded FAT32
     defaults); every unsupported op returns `NvfsError.Unsupported`. Keep it in
     `src/lib/gc_async_mut/svllm/nvfs_client/std_fs.spl`.
  2. **A2-direct:** CLI bypasses `NvfsClient` for now and calls `rt_file_*` externs
     directly; the trait is exercised later. Less architectural (AC-4 says "via the
     nvfs_client shim"), so option 1 is preferred.

  Recommend **option 1** — matches AC-4 wording and exercises R1/R3 semantics now.

### 2.5 `std.fs` surface (what's available today)

- Location: `src/lib/nogc_sync_mut/fs/` — only `__init__.spl`, `path.spl`, `path.smf`,
  `__init__.smf`, and `nvfs/` subdir (the parallel design's scaffolding; do NOT touch).
- `path.spl` exposes `Path` with `file_name`, `file_stem`, `is_file`, `is_dir`, `exists`,
  `create()` → bool (for directories).
- Byte I/O is in `std.io`, not `std.fs`: `std.io.{file_exists, is_dir}` is what path.spl
  re-exports.
- **No `rename`, no `fsync`, no `sync_dir` wrappers in std.fs.**

### 2.6 C runtime externs (the actual foundation)

Found in `src/runtime/runtime_native.c`:

| Extern | Line | C impl |
|---|---|---|
| `rt_file_open(path, mode) -> void*` | 210 | `fopen` |
| `rt_file_close(handle)` | 215 | `fclose` |
| `rt_file_move(src, dst) -> int` | 219 | `rename(src, dst)` (POSIX atomic within same dir) |
| `rt_file_read_bytes(path) -> char*` | 224 | — |
| `rt_file_write_bytes(path, data, len) -> int` | 229 | — |
| `rt_file_truncate(path, size) -> int` | 241 | — |

**Critical gaps:**
- **No `rt_file_fsync` / `rt_file_fdatasync` / `rt_dir_fsync`.** The only durability path
  today is "hope the kernel flushes". Required for R3 atomic-publish (must fsync data
  before rename, and fsync the directory after rename).
- No `rt_file_link` / `rt_file_unlink` (linkat-based atomic publish not possible).

---

## 3. Safetensors Test Fixture Strategy

**Constraint (from `feedback_interpreter_bulk_buffer.md`):** `bin/simple run` cannot
build multi-MiB `[u8]` buffers in reasonable time. Fixtures must be ≤64 KB when expressed
as `[u8]` literals in .spl, or generated via `rt_file_truncate` + streaming writes, or
checked in as binary files and read via `rt_file_read_bytes`.

**Smallest possible safetensors file (hand-computed, ~240 bytes):**

Two tiny tensors — a 2×2 F32 and a 3-element I64 — plus minimal metadata:

- Header JSON (ASCII, pretty-free):
  `{"w":{"dtype":"F32","shape":[2,2],"data_offsets":[0,16]},"b":{"dtype":"I64","shape":[3],"data_offsets":[16,40]}}`
  ≈ 114 bytes.
- 8-byte LE length prefix = 114.
- Payload = 16 bytes (F32×4) + 24 bytes (I64×3) = 40 bytes.
- **Total: 8 + 114 + 40 = 162 bytes.** Well under any buffer limit.

**Recommended approach (picked for A2):**

1. **Spec-driven generation:** a helper `fn build_tiny_safetensors() -> [u8]`
   under `test/unit/lib/gc_async_mut/svllm/model_executor/model_loader/` that returns
   the 162-byte buffer built via `push()` calls (no giant `[u8]` literal). Interpreter
   can handle this — it's O(200) pushes, not 10^6.
2. **Round-trip spec:** `safetensors_spec.spl` verifies
   `parse_safetensors_header(build_tiny_safetensors())` yields two entries with the
   right names, dtypes, shapes, and offsets.
3. **Packer round-trip spec:** `packer_roundtrip_spec.spl` writes the tiny buffer to
   `/tmp/svllm_fixture_<pid>.safetensors` via `rt_file_write_bytes`, invokes the CLI's
   `convert_pack()` entry, reads the produced `manifest.sdn` + `data-000.bin`, and
   re-parses.

**Reject alternatives:**
- Checking in a binary fixture under `test/fixtures/` works but scatters tests across
  directories; the spec-generator approach keeps everything co-located with the spec.
- `rt_file_truncate` + write-through streaming is overkill for 162 bytes; reserve that
  for future multi-chunk tests (e.g. 8 MiB pack files in integration tests).

---

## 4. Atomic-Publish Primitives Today

| Capability | Available? | Notes |
|---|---|---|
| Rename (same-dir) | Yes — `rt_file_move` → POSIX `rename(2)` | Atomic on ext4/xfs same-directory; **non-atomic on FAT32** (not a rename primitive per spec) |
| File fsync | **No** | Must file fs_request FS-REQ-fsync |
| Directory fsync | **No** | Must file fs_request FS-REQ-dir-fsync (needed to make rename durable) |
| Linkat / hardlink-based swap | **No** | Not needed for A2; note for future |
| O_TMPFILE / O_EXCL | **No extern wrappers** | `rt_file_open` uses fopen — no flag passthrough |
| Append-only enforcement (R1) | **No** | Kernel-level; svllm's R1 contract must be expressed via nvfs_client's `seal()` and the adapter is responsible for refusing writes post-seal. For std.fs adapter, "seal" = close + store expected digest; "publish_atomic" = two-step rename |

**A2 must file (AC-7)**:
1. `FS-REQ-001-fsync-primitive.md` — need `rt_file_fsync(handle) -> int` and
   `rt_dir_fsync(path) -> int` externs; current rename is not durable across power loss.
2. `FS-REQ-002-fat32-rename-atomicity.md` — FAT32 `rename` is not atomic (it's
   delete+create); document the gap and the degraded-mode contract
   (`NvfsError.Unsupported` from `publish_atomic`).
3. (Optional, nice-to-have) `FS-REQ-003-sha256-read-verify.md` — on read, request the
   fs layer verify a stored per-chunk digest before returning bytes (R1 sealed/pin
   invariant check).

---

## 5. Cooperative Providers

- **Codex CLI:** **available** at `/home/ormastes/.npm-global/bin/codex` (contradicts the
  A1 state file's "not used"). Can be used for the forked-research pass (Phase 2b) or a
  second opinion on the atomic-publish protocol in Phase 3. Strongly recommended for
  Phase 3 (arch) to review the two-step rename contract.
- **Gemini:** n/a — no UI surfaces in A2.

---

## 6. Preconditions & Commit Discipline Sanity Check

- `jj st` reports the working copy is **stale** (`operation 44ed79a84efa`). **Run
  `jj workspace update-stale` before the first commit in Phase 3+.**
- Disjoint scope for this track (from state.md):
  `src/lib/gc_async_mut/svllm/**`, `src/app/svllm_pack/**`,
  `test/unit/lib/gc_async_mut/svllm/**`, `doc/05_design/svllm/**`, and append-only edits
  to `doc/05_design/nvfs/svllm_requirements.md` (this track's own file).
- **Do not touch** `doc/05_design/nvfs_design.md`, `doc/05_design/nvfs/README.md` beyond
  cross-link follow-ups, `test/features/nvfs/`, `doc/08_tracking/feature_request/nvfs_requests.md`.
- Verify after each `jj split`: `git log --stat -1` shows only files in the disjoint
  scope.

---

## 7. Recommended A2 Work Order (for Phase 3 Architect to consume)

1. **Concrete fs shim first:** implement `nvfs_client/std_fs.spl` with just
   `create + write + close + publish_atomic + seal + query_caps` returning FAT32 defaults.
   Unblocks everything downstream.
2. **Real safetensors header parser** in `safetensors.spl`.
3. **Pack planner + writer** in `tensor_pack.spl` (plan chunks, compute digests,
   materialize bytes).
4. **Manifest serializer** in `manifest.spl` (SDN emit; parse kept as
   `Err(Malformed)` until A3).
5. **Wire CLI**: `svllm_pack convert <in> <out>` invokes
   safetensors parse → plan → write → manifest emit → two-step rename.
6. **Tests:** round-trip + error cases (empty input, truncated header, mismatched
   offsets, rename-collision).
7. **fs_requests:** file FS-REQ-001 and FS-REQ-002 as soon as the first
   `publish_atomic` path lands (captures real pain, not speculation).
8. **Upfront nvfs contribution:** append "R1 append_only object-class spec" +
   "R3 manifest-publish ordering rules" to `doc/05_design/nvfs/svllm_requirements.md`.

---

## 8. Open Questions for Architect (Phase 3)

1. Does `std.common.json` work from a `@gc` module? If not, how much of a minimal
   safetensors-JSON parser do we hand-roll in A2 vs. deferred to std.common?
2. Digest algorithm — BLAKE3 or SHA-256? The A1 comment says "BLAKE3/sha256" but
   `std.common.crypto` needs a look. Pick one for manifest v0; document in
   `svllm_requirements.md` R1.
3. Chunk size default — 2 MiB literal in `manifest_spec.spl` preamble. Make that a
   named constant `DEFAULT_PREFERRED_CHUNK_BYTES` in `tensor_pack.spl` or in the
   manifest module.
4. `std_fs.spl` adapter — does it live in `svllm/nvfs_client/` (coupled) or
   `src/lib/nogc_sync_mut/fs/nvfs_std/`? Coupled is faster; shared is right long-term.
   Recommend coupled for A2, lift in A3 refactor phase.

---

**End of audit.**
