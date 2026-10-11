# Phase 1 aspect-pack descriptor provider ownership (2026-10-11)

Status: production source repair; cached bootstrap diagnostics only. Admitted
pure-Simple compiler/core/MCP verification remains required before integration.

Current release `571d6cefe33` reproduces aspect-pack I/O 0/8 passing and declared
size-bound 2/5 passing. The cached Windows interpreter implements the separate
`rt_io_file_*` family as unavailable (`rt_io_file_open` returns -1), while the
raw `rt_open_fd` token owner consumed by `rt_mmap_raw` works on the same file.
An executed capability probe records old_fd=-1, raw_fd=1, a successful real file
mapping, byte 48 at offset 4101, and successful close/unmap statuses.

REQ-APKIO-OWNER-001: mapping descriptor tokens must come from the raw mapping
provider and be closed by that same provider; positioned-read tokens stay in
their own open/seek/read/close family.
REQ-APKIO-OWNER-002: exact unaligned binary ranges work on the supported raw
mapping provider without text conversion or whole-file reads.
REQ-APKIO-OWNER-003: declaration caps and EOF checks run before either read
path; index-cache tests retain precise error codes and byte-read counters.
REQ-APKIO-OWNER-004: supported positioned reads keep their bulk fast path;
fallback mapped copies use the existing native bulk byte-copy owner and release
the temporary mapping before returning their owned bytes.

The retained positioned-read path is used whenever its open succeeds. If open
fails, a bounded aligned mapping supplies the exact range. The mapping path uses
raw open/close consistently, and its copier delegates one borrowed-range read to
`native_mmap_read_bytes`/`rt_bytes_from_raw`, guarding window extents and pointer
addition before borrowing. No descriptor token crosses families; seek or read
failures on a successfully opened positioned provider do not switch providers.

The actual cached bulk symbol was verified on a real file mapping before use:
6 copied bytes preserve 255, embedded zero and the final byte, with successful
close/unmap. Native counterpart exists in `src/runtime/runtime_native.c` and the
interpreter registry, and the existing Simple owner exposes it.

Diagnostic artifacts live in `build/phase1-pack-io-20261011`. The first portable
window repair passes I/O 9/9 (including new binary/release control) and unchanged
size-bound 5/5, preserving every original error-code/counter assertion. A later
independent bulk-copy spec covers real native bytes, the 64 KiB mapping granule,
invalid geometry and pointer overflow: 4/4 passed, exit 0. That complete
interpreted diagnostic took 66.39 seconds including its 70,000-byte fixture
and 4,096 per-byte assertions; this is not a measured product-copy latency.
Earlier green specs were not replayed.
Source/spec hashes and log paths distinguish each verified source revision.
Producer SHA256: `15102d32226b3fbead63d3c63e33e99a6f0e9ffcddea06080fb65872445cbafb`.
No compiler rebuild, full-cohort replay, or prior stopped-preparation restart.

Pending admission: qualified pure-Simple compiler/lib/MCP/LSP checks, MCP
interpreter integration, core runtime smoke and MCP native smoke. Native Unix
positioned-read performance and concurrent truncation behavior remain preserved
by the unchanged fast path but were not executed on this Windows host. The
existing raw mapping contract supplies the fallback; no immutable archive,
TOCTOU, full Phase 1 or runtime release qualification is claimed.
