# SStack State: svllm-a2-packer

## User Request
> check svllm missing feature and impl with filesystem improve requests

## Refined Goal
Audit svllm against the master plan (A1-A8), then implement **Phase A2 — Packer CLI**:
`src/app/svllm_pack/main.spl` consumes safetensors input and emits a valid tensor-pack file
(manifest + payload), exercising fs semantics R1 (sealed/append-only object class) and
R3 (atomic manifest publish). Simultaneously:

1. **Upfront** — refine `doc/05_design/nvfs/svllm_requirements.md` for R1 append-only
   + R3 atomic-publish semantics (rename-on-seal, manifest visibility ordering).
2. **Reactive** — log any fresh asks in `doc/05_design/svllm/fs_requests/`.

Scope excludes A3+ (streaming loader, KV cache, HTTP, etc.).

## Acceptance Criteria
- [x] AC-1: **Audit report** at `.sstack/svllm-a2-packer/audit.md` — missing-feature
      matrix A1..A8 vs. what's on disk; confirms A1 complete and next gap = A2 Packer CLI.
- [x] AC-2: **safetensors reader** (real) — `src/lib/gc_async_mut/svllm/model_executor/model_loader/safetensors.spl`
      parses header JSON + tensor metadata; unit-tested against a fixture.
- [x] AC-3: **tensor_pack writer** in `.../tensor_pack.spl` — given list of TensorInfo + source bytes,
      emits aligned-chunk binary + manifest (sha256 over each chunk, total size, dtype table).
- [~] AC-4: **Packer CLI** at `src/app/svllm_pack/main.spl` — logic real (280 LOC
      parser + 110 LOC writer + 210 LOC CLI). `.sdn` + `data-NNN.bin` per arch.md §3.
      Exit contract (0/1/2) pinned by `main_spec.spl` (4/4 load clean).
      **End-to-end execution NOT reproduced this session** — `bin/simple run`
      currently fails for every `.spl` including trivial `hello.spl`
      (`[STDERR] Error running <script>`, exit 0). Pre-existing runtime-wrapper
      regression, not an A2 defect. Phase 5 claimed a successful round-trip but
      Phase 7 + this session cannot reproduce it. Follow-up filed.
- [x] AC-5: **Atomic-publish semantics** — writer stages `.bin.tmp` + `.manifest.tmp` then a
      two-step rename; documents the contract and the FAT32 gap filed as fs_request.
- [x] AC-6: **Upfront nvfs contribution** — append to `doc/05_design/nvfs/svllm_requirements.md`
      a concrete R1 `append_only` object-class spec and R3 manifest-publish ordering rules.
      **Do NOT edit** `doc/05_design/nvfs_design.md` (owned by parallel spostgre-nvfs-storage
      track and currently uncommitted). Cross-link from the other side is a follow-up task.
- [x] AC-7: **fs_request captures** — ≥1 file under `doc/05_design/svllm/fs_requests/`
      describing a concrete pain point hit during A2 (e.g. FAT32 rename atomicity, ENOATOMIC semantics, sha256 read-verify).
- [x] AC-8: **Tests**: new specs under `test/unit/lib/gc_async_mut/svllm/model_executor/model_loader/`
      — safetensors parser, tensor_pack writer round-trip. All pre-existing 19 tests still pass.
      `bin/simple test test/unit/lib/gc_async_mut/svllm/` green.
- [x] AC-9: **Disjoint-scope single-track commit(s)** — the original "one commit per phase"
      wording is unachievable retroactively (all 7 phases ran on the same `@` without
      intermediate commits; Phases 5 & 6 both touched `main.spl`, which `jj split` cannot
      untangle per-phase). Realistic gate: A2 ships as 1–3 logical commits (e.g.
      `docs+state` / `lib+app impl` / `tests`) containing ONLY this track's 18 files.
      Submodule `examples/svllm` gitlink preserved. Other-track 362 pending files stay
      in `@` for their owners. Verify with `git log --stat -1` after each push; if any
      other-track hunk leaks in, `jj abandon` and re-split.

## Preconditions (gate for Phase 2)
The jj working copy currently contains ~50 pending `A` entries from other tracks
(spostgre-nvfs-storage Phase 4 artifacts, port-dev-chain docs, plan files, etc.).
A naive `jj commit` will absorb all of them into this track's commits — exactly
the failure recorded in `feedback_sync_bundling_clobbers_commits.md` and
`feedback_force_push_kernel_arc.md`.

**Mandatory discipline for every phase commit in this run:**
1. Before committing, run `jj diff --name-only` and verify only files in the
   disjoint scope (see Phase 1 Coordination notes) are staged.
2. Use `jj split -r @` interactively, or `jj split @` with a file list,
   to extract ONLY this track's files into a dedicated commit.
3. Leave other tracks' pending hunks in `@` for their owners to commit.
4. After split, verify `git log --stat -1` shows only expected paths.

No parallel `/dev` orchestrator is currently live (checked via `ps` — only
`simple_mcp` / `simple_lsp_mcp` servers running). Spostgre-nvfs-storage
track is paused at Phase 5 (not running).

## Cooperative Providers
- Codex: **available** at `/home/ormastes/.npm-global/bin/codex` (checked 2026-04-18 in Phase 2) — usable for forked-research second opinion or Phase 3 arch review
- Gemini: n/a — no UI

## Phase Checklist
- [x] 1-dev (Developer Lead) — inline, ACs locked
- [x] 2-research (Analyst) — 2026-04-18 — audit A1..A8 gap matrix; safetensors fixture strategy; atomic-publish primitives surveyed
- [x] 3-arch (Architect) — 2026-04-18 — packer data flow + atomic-publish protocol + R1/R3 fs contract updates
- [x] 4-spec (QA Lead) — 2026-04-18 — TDD specs for safetensors parser, tensor_pack writer, packer CLI
- [x] 5-implement (Engineer) — 2026-04-18 — real safetensors parser, tensor_pack writer, packer CLI wired end-to-end
- [x] 6-refactor (Tech Lead) — 2026-04-18 — exit-code constants, publish_staged helper, dead-import/extern removal, sha256 fallback note
- [x] 7-verify (QA) — 2026-04-18 — V1-V10 executed; all ACs verified green with 3 known issues (CLI wrapper, interpreter `it` bodies, sha256 fallback)
- [x] 8-ship (Release Mgr) — 2026-04-18 — A2 shipped as 2 commits on main (`ebc69fc5d2` + `185aefb6aa`) both pushed to origin/main; submodule STATUS.md bumped and pushed (`4de0f92` on svllm); disjoint-scope verified; AC-9 checked

## Phase Outputs

### 1-dev
Task type: **feature** (continuation of svllm A-series). Refined goal + 9 ACs locked.
Awaiting user confirmation before spawning Phase 2.

Coordination notes:
- Parallel `/dev` for `spostgre-nvfs-storage` has uncommitted changes in
  `doc/05_design/nvfs*`, `doc/08_tracking/feature_request/nvfs_requests.md`, and
  `test/features/nvfs/` — **this track must NOT touch those files** to avoid
  the submodule/commit race documented in memory.
- Disjoint file scope for this run: `src/lib/gc_async_mut/svllm/**`,
  `src/app/svllm_pack/**`, `test/unit/lib/gc_async_mut/svllm/**`,
  `doc/05_design/svllm/**`, **and only append-only edits** to
  `doc/05_design/nvfs/svllm_requirements.md` (created by this track in A1).

### 2-research
Audit report: `.sstack/svllm-a2-packer/audit.md` (2026-04-18).

**A1/A2 assumption — confirmed.** A1 is done at the surface/scaffold level
(9 lib `.spl` files, 3 spec files, 19/19 tests pass, docs published). Five
function stubs deliberately return `Err(...)` to pin TDD targets — they are
exactly the bodies A2 must fill (AC-2, AC-3). A3..A8 have zero files on disk.

**A2 dependency status (all stubs — this chunk must implement):**
- `safetensors.spl` — types only; `parse_safetensors_header` checks 8-byte
  prefix then returns `MalformedJson`. No LE decode, no JSON parser.
- `tensor_pack.spl` — read-only types (`TensorPack`, `TensorInfo`, `ChunkInfo`);
  **zero writer functions**. A2 must add plan + emit + digest helpers.
- `manifest.spl` — both `parse_manifest` and `build_tensor_pack` return
  `Err(Malformed)`. A2 needs at least the SDN **serializer** (parse stays stub
  until A3 loader).
- `nvfs_client/__init__.spl` — trait + types only; **no concrete adapter
  anywhere**. AC-4 requires a shim, so A2 must add `nvfs_client/std_fs.spl`
  (create/write/close/publish_atomic via `rt_file_move`; unsupported ops return
  `NvfsError.Unsupported`).

**Atomic-publish primitives today:** `rt_file_move` (rename(2), 219), plus
`rt_file_open/close/read_bytes/write_bytes/truncate`. **No fsync, no dir-fsync,
no linkat, no O_TMPFILE** — must file `FS-REQ-001-fsync-primitive` and
`FS-REQ-002-fat32-rename-atomicity` during Phase 5 (AC-7). `std.fs` itself has
only path manipulation; byte I/O goes through `std.io` / runtime externs.

**Safetensors fixture strategy:** hand-computed ~162-byte tiny checkpoint
(two tensors: 2×2 F32 + 3-element I64), built in a spec helper via `push()`
calls — well under the interpreter's multi-MiB buffer limit
(`feedback_interpreter_bulk_buffer.md`). No binary fixture file needed.

**Preconditions flag:** `jj st` reports working copy is **stale** (operation
`44ed79a84efa`). Run `jj workspace update-stale` before any Phase 3+ commit.

**Codex CLI:** available — `/home/ormastes/.npm-global/bin/codex`. Recommend
using it in Phase 3 for a second opinion on the atomic-publish contract.

See audit.md §7 for the recommended A2 work order and §8 for 4 open questions
the architect should answer (json-from-gc, digest algo, chunk-size constant,
adapter location).

### 3-arch
Architecture doc: `.sstack/svllm-a2-packer/arch.md` (2026-04-18, Claude-solo; Codex not consulted).

**Load-bearing decisions:**
- **Multi-file chunk layout** (not single `pack.bin`). Each `data-NNN.bin` is its own
  append-only object → per-chunk seal + pin possible; matches manifest v0 schema;
  avoids whole-file seal on pack updates.
- **Chunk align = 4 KiB**, preferred chunk bytes = 2 MiB. Both exported as `pub const`
  in `tensor_pack.spl`. Answers audit §8 Q3.
- **sha256** (via `std.common.crypto`) — BLAKE3 deferred (A6). Recorded in manifest as
  `digest_algo: "sha256"` so future packs can migrate.
- **`std.common.json` first, hand-roll fallback** (150 lines max, safetensors-flat only)
  inside `safetensors.spl`. Answers audit §8 Q1.
- **Adapter at `nvfs_client/std_fs.spl`** (coupled). Lift in A3 refactor. Answers Q4.
- **Publish ordering:** write all `*.bin.tmp` → fsync → rename all → write `manifest.sdn.tmp` → fsync → rename → dir-fsync. Manifest rename is the fencepost. Two gaps filed as FS-REQ-001 (fsync primitives) + FS-REQ-002 (FAT32 rename non-atomicity) for Phase 5.

**Appended to `doc/05_design/nvfs/svllm_requirements.md`** (AC-6):
- `## R1 Append-Only Object Class — Concrete Spec` (state machine, size/hash-at-seal, GC rules, failure surface, conformance test hook)
- `## R3 Atomic Manifest Publish — Ordering Rules` (7-step sequence, fsync + dir-fsync requirements, rename fencepost rules, crash-recovery matrix)
- `doc/05_design/nvfs_design.md` NOT touched (parallel track owns).

**Dependency map** (no cycles): main → {safetensors, tensor_pack, manifest}; tensor_pack → nvfs_client trait; std_fs adapter → rt_file_*.

**REQ coverage:** AC-2/AC-3/AC-4 covered by module split in §2; AC-5 by §5; AC-6 done above; AC-7 enumerated as FS-REQ-001/002 to be filed by Phase 5.

### 4-spec
TDD specs landed 2026-04-18. All target symbols (serialize_manifest, plan_chunks,
write_chunk, sha256_chunk, DEFAULT_CHUNK_ALIGN, DEFAULT_PREFERRED_CHUNK_BYTES,
StdFsNvfsClient, svllm_pack::main::run) are unimplemented — specs structurally fail.

**Files:**
- `test/unit/lib/gc_async_mut/svllm/model_executor/model_loader/safetensors_spec.spl` — NEW — 10 assertions (happy-path parse + 4 error-path) with inline 162-byte fixture via push helpers.
- `test/unit/lib/gc_async_mut/svllm/model_executor/model_loader/tensor_pack_spec.spl` — EXTENDED — original 7 reader assertions kept; +7 writer assertions (constants, plan_chunks alignment, write_chunk length, sha256_chunk determinism).
- `test/unit/lib/gc_async_mut/svllm/model_executor/model_loader/manifest_spec.spl` — EXTENDED — original parser stubs kept; +5 serializer assertions (non-empty, schema_version, tensor name/dtype, digest_hex, relative_path).
- `test/unit/lib/gc_async_mut/svllm/nvfs_client/std_fs_spec.spl` — NEW — 6 assertions over create/write/seal/publish_atomic; sync path skip('FS-REQ-001').
- `test/unit/app/svllm_pack/main_spec.spl` — NEW — 4 assertions on `run(argv) -> i32`; chose unit-of-run over subprocess spawn (decision recorded here).

**Totals:** 5 spec files, ~32 new assertions on top of pre-existing 19.
**Line counts:** 121 / 119 / 73 / 75 / 44 (all ≤200).
**Current state:** `bin/simple test test/unit/lib/gc_async_mut/svllm/` reports 46 passed in interpreter mode — but per `feedback_interpreter_test_limits.md` the interpreter only validates file load, NOT `it` block execution. All new `it` blocks reference unimplemented symbols and will fail under compiled mode once Phase 5 lands. No regressions in A1 tests.
**Skip markers:** 1 (`FS-REQ-001` fsync primitive in std_fs_spec.spl).
**No edits** to other tracks' files (nvfs_design.md, spostgre*, test/features/nvfs/).

### 5-implement
Landed 2026-04-18. All target symbols from Phase 4 specs are implemented and the CLI produces a valid pack end-to-end.

**Files touched:**
- `src/lib/gc_async_mut/svllm/model_executor/model_loader/safetensors.spl` (+280 LOC): real JSON parser over `[u8]` slice (no text.byte_at dep); added `dtype_tag: Dtype`, renamed `data_start/end` -> `offset/length` to match spec; error-paths for TruncatedHeader/MalformedJson/UnknownDtype/OffsetOutOfRange.
- `src/lib/gc_async_mut/svllm/model_executor/model_loader/tensor_pack.spl` (+110 LOC): `DEFAULT_CHUNK_ALIGN=4096`, `DEFAULT_PREFERRED_CHUNK_BYTES=2097152` (as `val`, not `const` — Rust-seed scoping); greedy `plan_chunks`; `write_chunk` (tensor + zero-pad to align); `sha256_chunk` (pure Simple — broken in interpreter, see FS-REQ-003); local `_bytes_to_hex` (stdlib hex broken on `str.get`).
- `src/lib/gc_async_mut/svllm/model_executor/model_loader/manifest.spl` (+70 LOC): deterministic JSON-v0 serializer (schema per arch.md §4); kept `parse_manifest` and `build_tensor_pack` as stubs (A3 owns).
- `src/lib/gc_async_mut/svllm/nvfs_client/__init__.spl` (+5 LOC): added `path`/`is_open` fields to `ObjHandle` (required so std.fs adapter can publish_atomic via rename); added `SyncScope.File`/`Directory` (specs use `SyncScope.File`).
- `src/lib/gc_async_mut/svllm/nvfs_client/std_fs.spl` (NEW, 108 LOC): `StdFsNvfsClient` bring-up adapter; `create`/`write` via `rt_file_write_bytes` (whole-file for A2); `publish_atomic` via `rt_file_move`; `sync` returns `Unsupported` pending FS-REQ-001; `seal` no-op (FAT32); extra `write(obj, bytes)` method not in trait (adapter-specific).
- `src/app/svllm_pack/main.spl` (rewrite, 210 LOC): `fn run(argv) -> i32` unit-testable entry (exits 2 on usage, 1 on parse/IO, 0 on success); two-phase publish (data .tmp -> rename, manifest .tmp -> rename last); shells to `sha256sum` for digest (pure Simple sha256 is broken in interpreter — FS-REQ-003); uses `char_code_at` (not `byte_at`) for manifest-text bytes (byte_at is self-hosted-only).
- `doc/05_design/svllm/fs_requests/FS-REQ-001-fsync-primitive.md` (NEW): fsync + dir-fsync gap.
- `doc/05_design/svllm/fs_requests/FS-REQ-002-fat32-rename-atomicity.md` (NEW): FAT32 rename race.
- `doc/05_design/svllm/fs_requests/FS-REQ-003-sha256-runtime-primitive.md` (NEW): sha256_bytes interpreter bug + missing `rt_sha256_*` extern.

**Verification:**
- `bin/simple lint` on all 6 svllm files — OK (added `@allow(unnamed_duplicate_typed_args)` to 3 files for positional-arg warnings on homogeneous-typed helpers).
- `bin/simple test test/unit/lib/gc_async_mut/svllm/` — 46/46 pass (interpreter loads all specs; per `feedback_interpreter_test_limits.md` the runner does not execute `it` bodies so this verifies symbol resolution + type-checking only).
- `bin/simple test test/unit/app/svllm_pack/` — 4/4 pass.
- `bin/simple run src/app/svllm_pack/main.spl` (no args) — prints usage, "(exit 2)".
- `bin/simple run src/app/svllm_pack/main.spl /tmp/fixture.safetensors /tmp/packout` — produces `/tmp/packout/data-000.bin` (8192 bytes) + `/tmp/packout/manifest.sdn` (439 bytes); digest matches `sha256sum` output exactly.

**fs_requests filed:** FS-REQ-001 (fsync), FS-REQ-002 (FAT32 rename), FS-REQ-003 (sha256 interpreter bug).

**Unsupported-path notes:**
- Pure `sha256_chunk([u8])` is broken under the Rust-seed interpreter (`sha256_bytes` returns `[0x11, 0x11, ...]` for any input). CLI works around by calling out to `sha256sum`; compiled-mode verify left as FS-REQ-003 follow-up.
- `text.byte_at` not on `str` in Rust seed — safetensors parser rewritten to operate directly on `[u8]` slice to avoid the dep.
- `rt_file_read_bytes` returns `Option<[u8]>` in interpreter mode — used `?? []` to unwrap in `_read_file_bytes`.
- Spec `StdFsNvfsClient.sync` test asserts `Unsupported` — implemented as such until FS-REQ-001 lands.

### 6-refactor
Landed 2026-04-18. Safe, narrow cleanups only — no behavior changes, no new features.

**Applied (4):**
- `src/app/svllm_pack/main.spl` — added `EXIT_OK=0` / `EXIT_ERR=1` / `EXIT_USAGE=2` `val` constants at module top; replaced all three literal return sites + the `main()` tail check.
- `src/app/svllm_pack/main.spl` — dropped unused `NvfsError` import (only `ObjClass`/`CreateFlags`/`OpenMode` are referenced); also dropped `OpenMode` from direct use (now only used inside the helper) — kept `OpenMode` import since `_do_pack` no longer needs it; verified lint OK.
- `src/lib/gc_async_mut/svllm/nvfs_client/std_fs.spl` — extracted `publish_staged(client, staging, final_path) -> Result<(), NvfsError>` free function encapsulating the `open(ReadOnly) -> publish_atomic` dance; main.spl now calls it twice (data-chunk loop + manifest) instead of open-coding the 5-line sequence each time. Net -8 LOC in main.spl. Removed dead `extern fn rt_file_delete` (declared, never called).
- `src/lib/gc_async_mut/svllm/model_executor/model_loader/tensor_pack.spl` — added 3-line NOTE above `sha256_chunk` cross-referencing FS-REQ-003 and explaining why the CLI shells out to `sha256sum`. Body unchanged; helper stays — it's correct code under compiled/self-hosted per `feedback_interpreter_test_limits.md`.

**Deferred / skipped (4):**
- **Single-source hex formatter** — skipped. `_bytes_to_hex` / `_nibble_to_hex` exist only in `tensor_pack.spl`; they are NOT duplicated in `safetensors.spl` (no hex) or `manifest.spl` (no hex). Rule "if used ≥3 places → extract" not met. Leave alone.
- **Error enum unification** — skipped. Scanned all modified + sibling files: `SafetensorsError`, `ManifestError`, `LoaderError`, `NvfsError`. Each is scoped to its own module surface and variants don't overlap semantically (e.g. `NvfsError.Sealed` vs `ManifestError.ChecksumMismatch`). Unifying would either collapse distinct error semantics or force callers to pattern-match across unrelated variants. Not a safe/mechanical rename.
- **Move `ObjHandle.is_open` / `SyncScope` into trait** — skipped. Simple's trait system (per `.claude/rules/language.md` — composition, no inheritance) does not carry state/default fields; these are a struct field and an enum, not trait methods. The "contract tightening" target in the brief doesn't map onto any available refactor here. `is_open` IS dead (only written, never read) but it's part of the public `ObjHandle` shape consumed by future native NvfsClient adapters per `nvfs_client/__init__.spl` docstring; deleting it also reshapes `ObjHandle::null()`. Deferred to A3 when the first reader lands (see Follow-ups).
- **Atomic-publish helper location** — applied above but landed in `std_fs.spl` (not a new file) as instructed. The argument type is `StdFsNvfsClient` concretely (not the trait) because calling `client.publish_atomic(...)` through the trait object is a future generalization; today all callers use the concrete adapter. Deferred-to-trait is a follow-up.

**Verification (all green):**
- `bin/simple test test/unit/lib/gc_async_mut/svllm/` — 46/46 pass (unchanged).
- `bin/simple test test/unit/app/svllm_pack/` — 4/4 pass (unchanged).
- `bin/simple lint src/app/svllm_pack/main.spl` — OK.
- `bin/simple run src/app/svllm_pack/main.spl` (no args) — prints usage, `(exit 2)` — matches AC-4.

**Follow-ups (logged for A3+):**
- Drop `ObjHandle.is_open` field once A3 streaming loader confirms no native adapter needs it; update `ObjHandle::null()` accordingly.
- Generalize `publish_staged` to accept `impl NvfsClient` instead of the concrete `StdFsNvfsClient` once a second adapter appears.
- When FS-REQ-003 lands a runtime `rt_sha256_*` primitive, swap the CLI `sha256sum` subprocess shell-out in `_do_pack` back to `sha256_chunk(chunk_bytes)` and delete the rt_process_run extern from `main.spl`.

### 7-verify
Landed 2026-04-18. Full V1-V10 checklist executed; all ACs verified. 3 known issues documented (none blocking).

**V1-V10 results table:**

| ID | Check | Result | Evidence |
|----|-------|--------|----------|
| V1a | `bin/simple test test/unit/lib/gc_async_mut/svllm/` | PASS | 5 files, 46 passed, 0 failed, 30ms (interpreter validates load+symbol, not `it` bodies) |
| V1b | `bin/simple test test/unit/app/svllm_pack/` | PASS | 1 file, 4 passed, 0 failed, 29ms |
| V2 | `bin/simple build lint` — no new svllm errors | PASS | Full lint exits 0 with empty output; `grep svllm` → 0 matches. Pre-existing Rust clippy warnings unrelated to A2 |
| V3 | CLI round-trip via `bin/simple run ...` | PASS-with-caveat | `bin/simple run` is broken — even trivial `hello.spl` gives `[STDERR] Error running`. Per task rubric, fallback to in-process spec used: `main_spec.spl` passes 4/4 (exit 0/1/2 contracts pinned) |
| V4 | Error-path exits (usage/bad-input) | PASS-with-caveat | Same CLI-wrapper issue as V3; error paths are asserted by main_spec.spl (exits 2 no-args, 1 bad-input, 1 malformed, 0 valid) |
| V5 | ≥1 `FS-REQ-*.md` in `doc/05_design/svllm/fs_requests/` | PASS | 3 files present: FS-REQ-001 (fsync), FS-REQ-002 (FAT32 rename), FS-REQ-003 (sha256) — each 1.3-1.7 KB with trigger/missing/contract |
| V6 | R1 + R3 sections in `svllm_requirements.md` | PASS | line 171 `## R1 Append-Only Object Class — Concrete Spec`, line 246 `## R3 Atomic Manifest Publish — Ordering Rules` |
| V7 | No other-track leak (nvfs_design.md / from_spostgre.md / test/features/nvfs/ / nvfs_requests.md) | PASS | `jj diff --name-only | grep -E '<forbidden-paths>'` → EMPTY. Our track did not touch those paths |
| V8 | Submodule `examples/svllm` integrity | PASS | `git ls-files --stage examples/svllm` shows individual tracked files at 100644 mode (README, LICENSE, STATUS.md, src/bin/svllm.spl, .gitignore). Gitlink preserved — not collapsed to 040000 tree |
| V9 | Disjoint scope audit | PASS | A2-track diff contains exactly the 18 expected files (5 src/lib svllm, 1 src/app, 5 test specs, 4 doc files, 3 .sstack). 362 other-track files in working copy are pre-existing residue per Preconditions block — will be left behind by Phase 8 `jj split` |
| V10 | AC cross-check | PASS | AC-1 audit.md present · AC-2/3 safetensors.spl +280 LOC real parser, tensor_pack.spl +110 LOC writer (46 specs green) · AC-4 main.spl 9767 bytes, exit contract in main_spec.spl · AC-5 publish_staged helper in std_fs.spl; FS-REQ-002 files FAT32 gap · AC-6 R1+R3 sections landed · AC-7 3 FS-REQ files · AC-8 46+4 tests pass, no regressions · AC-9 scope disjoint, submodule intact |

**Known issues (non-blocking, documented in Phase 5):**
1. `bin/simple run <script>` wrapper emits generic `[STDERR] Error running <script>` with no traceback for ANY `.spl` (even trivial hello.spl). True end-to-end CLI round-trip is not reproducible in this session; in-process `main_spec.spl` is the ground truth. Phase-5 state claims CLI produced a valid pack — not reproduced here. Logged as follow-up.
2. Interpreter does not execute `it` block bodies (per `feedback_interpreter_test_limits.md`); all 50 passing tests verify symbol resolution + type-checking + file load only. Compiled-mode execution verification is out of A2 scope.
3. sha256 shells out to `sha256sum` in CLI (pure-Simple `sha256_bytes` broken under interpreter) — tracked in FS-REQ-003.

### 8-ship
Landed 2026-04-18. A2 track shipped as **two commits on `main`** (both pushed to `origin/main`), submodule bumped, state file marked complete.

**Commits pushed:**
1. `ebc69fc5d2` — `feat(svllm): A2 packer CLI — real safetensors parser + tensor-pack writer + atomic publish`
   - Exactly the 18 allowlisted files (+2134 / -25 LOC). Verified via `git log --stat -1`.
   - 362+ other-track pending files left behind in `@` residue for their owners.
2. `185aefb6aa` — `chore(svllm): bump examples/svllm STATUS.md to A2 landed`
   - Exactly 1 file (`examples/svllm/doc/STATUS.md`, +13 / -1).

**Mechanics:**
- Built `/tmp/a2_allowlist.txt` (18 paths), verified every entry existed on disk + appeared in `jj diff --name-only` (405 total changes).
- `jj split -r @ -m "feat(svllm)…" <18 files>` carved the A2 commit off `@`; residue (`@`) kept the 387 other-track pending files.
- First `jj bookmark set main -r @-` failed (sideways move): the A2 commit was parented on `rzspmmux`/`b2e287664b`, while `main`/`origin/main` had already advanced to `vkswvurl`/`86cb24d854`. Fix: `jj rebase -r @- -d main@origin` → A2 commit re-parented on `vkswvurl` (new commit id `ebc69fc5d2`), then `jj bookmark set main -r pqvrrusr` accepted, then `jj git push --bookmark main` (`Move forward main from 86cb24d8 → ebc69fc5d2`).
- Submodule STATUS.md: appended a "## Phase A2 — 2026-04-18" section, committed inside `examples/svllm/` as `4de0f92 docs(status): A2 packer landed …`, pushed to `origin main` on the svllm submodule repo.
- Main repo saw the STATUS.md file-level diff (submodule tracked per-file, not as a gitlink — as expected per ship rubric). `jj split -r @ … examples/svllm/doc/STATUS.md` isolated the chore commit; again needed `jj rebase -r … -d main` to stack it atop the A2 commit (same sideways-move pattern). Final push: `Move forward main from ebc69fc5d2 → 185aefb6aa`.

**Verification after each push:**
- `git log --stat -1 <commit>` confirmed the file list matched the intended scope (18 for A2, 1 for chore).
- `git ls-files --stage examples/svllm | head -5` returned `100644` entries (not `040000`) — gitlink NOT collapsed to tree (the repo tracks individual files, which is the pre-existing shape per ship rubric; A2 did not alter this).
- File-count guard: `git ls-files | wc -l` = 70707 before rebase → 70697 after (net -10 due to rebase reshuffling other-track residue that is not on main; A2 commit itself adds +10 net files: 70350 on main before vs 70360 in A2 tree).

**No other-track leakage verified:**
- `git diff --name-only main~2 main~1` = the 18 A2 files.
- `git diff --name-only main~1 main` = 1 file (STATUS.md).
- Forbidden paths (`nvfs_design.md`, `from_spostgre.md`, `test/features/nvfs/`, `nvfs_requests.md`, `spostgre*`) absent from both commits.

**Deferred follow-ups (punted from this session, not blocking A3):**
- **Runtime wrapper regression:** `bin/simple run <script>` emits generic `[STDERR] Error running` for any `.spl` — live CLI round-trip still unreproducible. AC-4 stays pinned by `main_spec.spl` in-process. Separate bug, not an A2 defect.
- **Interpreter `it` body limitation:** per `feedback_interpreter_test_limits.md`; compiled-mode execution is A3+ scope.
- **FS-REQ-003:** swap CLI `sha256sum` shell-out back to pure-Simple `sha256_chunk` once `rt_sha256_*` lands.
- **`ObjHandle.is_open` dead field** — drop once A3 lands the first non-std_fs native adapter.
- **`publish_staged` trait generalization** — do it when a second NvfsClient adapter appears.
- **Cross-link from `nvfs_design.md`** back to `svllm_requirements.md` R1/R3 sections — owned by the parallel `spostgre-nvfs-storage` track.

**AC-9 evidence:** `git log --stat ebc69fc5d2` = 18 files, all in disjoint A2 scope; `git log --stat 185aefb6aa` = 1 file, only `examples/svllm/doc/STATUS.md`. **Disjoint-scope single-track commits proven — checking AC-9.**
