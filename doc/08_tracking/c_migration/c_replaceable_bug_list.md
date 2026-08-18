# C-replaceable inventory — bug list (generated from Wave-1 audit, 2026-08-18)

Projection of `c_migration_inventory.sdn` + the Wave-1 C audit
(`doc/03_plan/infra/binary_runtime_hardening/wave1_audit_results_2026-08-18.md`).
Scope: 107 non-vendored `.c` files, 51,156 lines under `src/runtime/`.
Classification per the frozen design §13: every entry below is project-owned C
that Simple should be able to replace; inability discovered during migration
becomes a SIMPLE-CAPABILITY bug, not a reason to keep the C.

## Status legend
`done` = migrated with differential + regression evidence · `planned` = next
tranches · `assess` = needs per-symbol caller analysis before commitment.

| Bug ID | C unit | Lines | Class | Replacement path | Status |
|---|---|---:|---|---|---|
| C-MIG-0001 | runtime_legacy_core.c:rt_crc32_text | ~15 | product algorithm | std.nogc_sync_mut.compression.gzip.crc32_text | **done** (5/5 differential, 35/35 regression, C retained as oracle) |
| C-MIG-0002 | runtime_simd_dispatch.c | 2,208 | product algorithm | pure-Simple scalar path + SIMPLE-CAPABILITY bug for vector intrinsics | planned |
| C-MIG-0003 | runtime_pool.c | 1,292 | runtime primitive | std.memory provider (sanctioned alias boundary) | planned |
| C-MIG-0004 | runtime_native.c (11,139 lines, monolith) | 11,139 | runtime primitive (mixed) | split by symbol family first; string/array/dict value ops are the Simple-replaceable half | assess |
| C-MIG-0005 | runtime.c | 3,456 | runtime primitive | core value/entry glue — provider boundary, not full rewrite | assess |
| C-MIG-0006 | runtime_process.c | 2,297 | platform shim | retain minimal syscall shim; command construction/decoding to Simple (HAL split per design §14) | planned |
| C-MIG-0007 | runtime_thread.c | 2,005 | platform shim | same HAL split: sync-primitive shim stays, orchestration to Simple | planned |
| C-MIG-0008 | platform/async_linux_epoll.c / async_windows.c / async_linux_uring.c | ~2,800 | platform shim | HAL contract (BlockDevice/EventLoop pattern, design §14 step 1) | planned |
| C-MIG-0009 | database/sqlite glue (2 files) | 1,111 | third-party wrapper | facade stays; owned glue logic (row/value marshalling) to Simple | assess |
| C-MIG-0010 | openssl/tls glue (3 files) | 968 | third-party wrapper | facade stays; owned handshake state tracking to Simple; KAT + interop corpus mandatory | assess |
| C-MIG-0011 | time/timestamp (2 files) | 265 | runtime primitive | provider alias (clock syscall is the boundary) | planned |
| C-MIG-0012 | bootstrap/startup (6 files) | 327 | bootstrap stage | staged self-hosting plan; not general-migration scope | planned |
| C-MIG-0013 | mcp shim | 0 (deleted 2026-08-18) | DELETED: forward-cache row mapped a symbol (mcp_stdio_read_message) that existed nowhere; pure-Simple read_stdin_message is the real implementation | runtime_mcp_core.c + decls + 4 link/roster refs + forward-cache row removed; smoke test retargeted | done |
| C-MIG-0014 | wasm shim (scv_wasm_shim.c) | 459 | platform ABI shim | retain; external SDK boundary (guard SKIPs it already) | assess |
| C-MIG-0015 | media wrappers (sdl2/sdl3/glfw/audio/font, 23 files) | 5,409 | third-party wrapper | facades retained; owned pixel/format conversion helpers to Simple | assess |
| C-MIG-0016 | src/runtime/test/** (27 files) | 3,870 | conformance oracle | test-only, VERIFIED never production-linked (capsule selfcheck binaries only) | **verified** |
| C-MIG-0017 | memory/memtrack/packed_span (excl. pool) | 1,146 | runtime primitive | provider boundary + Simple-side accounting | planned |
| C-MIG-0018 | hosted_win32.c + scilib/rocm/cuda shims | ~3,000 | platform shim | retain thin ABI shims; declared-retained entries in registry | assess |
| C-MIG-0020 | runtime_native.c:rt_hash_text + runtime_legacy_core.c:rt_str_hash | ~15 | product algorithm | std.hash text.hash() / rt_hash_text ABI bridge (already implemented, proven equivalent) | **done** (7/7 differential incl. KAT + UTF-8 + boundary lengths, C retained as oracle) |
| C-MIG-0021 | runtime_native.c:rt_string_to_int | ~10 | product algorithm | std.common.text.parse_i64 (text.spl, already implemented, proven equivalent on well-formed input) | **done** (7/7 differential incl. KAT + 100-vector shared branch-covering bulk loop with perf evidence, C retained as oracle; failure-sentinel divergence 0-vs--1 on malformed/empty input documented not asserted-equal; perf ratio ~1.59x, under 2x threshold) |
| C-MIG-0022 | runtime_simd_utf8.c:rt_text_validate_utf8 | ~5 | product algorithm | pure-Simple validated_utf8_bytes_to_text_linear (base_encoding/utilities.spl, already implemented, proven equivalent) | **done** (4/4 differential incl. KAT + malformed-byte discrimination + 88-vector bulk loop, C retained as oracle; PERF FINDING: Simple ~32.9x slower under interpreter, recorded not hidden) |
| C-MIG-0023 | runtime.c:rt_base64url_encode/rt_base64url_decode | ~60 | product algorithm | std.common.base_encoding.base64.{base64url_encode,base64url_decode} (base64.spl, already implemented, proven equivalent) | **done** (6/6 differential incl. RFC 4648 §10 KAT + 100-vector shared branch-covering bulk loop with UTF-8, C retained as oracle; PERF FINDING: Simple ~44.1x slower under interpreter, recorded not hidden) |
| C-MIG-0024 | runtime_native.c:rt_string_rfind | ~10 | product algorithm | std.common.string_core.str_last_index_of (string_core.spl, already implemented, proven equivalent) | **done** (5/5 differential incl. KAT + overlapping/full-match edge cases + 100-vector shared branch-covering bulk loop, C retained as oracle; PERF FINDING: Simple ~4.4x slower under interpreter, recorded not hidden) |
| C-MIG-0025 | runtime_native.c:rt_string_ends_with | ~6 | product algorithm | std.common.string_core.str_ends_with (string_core.spl, already implemented, proven equivalent) | **done** (6/6 differential incl. KAT + multibyte-UTF-8-suffix + full/near-full-match edge cases + 100-vector shared branch-covering bulk loop, C retained as oracle; ratio ~1.8x under interpreter, below the 2x threshold, no PERF finding) |
| C-MIG-0026 | runtime_native.c:rt_raw_i64_to_string | ~10 | product algorithm | std.common.convert.i64_to_text (convert.spl, already implemented, proven equivalent) | **done** (6/6 differential incl. KAT + i64::MIN/MAX boundaries + digit-count-transition edge cases + 100-vector shared branch-covering bulk loop, C retained as oracle; PERF FINDING: Simple ~2.3x slower under interpreter, recorded not hidden. Rejected candidates: rt_string_starts_with — unregistered in interpreter extern dispatch; rt_text_to_lower_ascii/str_to_lower — str_to_lower crashes on multibyte UTF-8 input, filed as bug str_to_lower_upper_crash_on_multibyte_utf8_2026-08-18; rt_string_rfind/str_last_index_of — already covered by C-MIG-0024) |
| C-MIG-0027 | runtime_native.c:rt_char_from_code | ~17 | product algorithm | std.common.string_core.char_from_code (string_core.spl, already implemented, proven equivalent) | **done** (6/6 differential incl. KAT + all 4 UTF-8 encoding-length classes + invalid-codepoint/surrogate-range edge cases + 100-vector shared branch-covering bulk loop, C retained as oracle; PERF FINDING: Simple ~3.5x slower under interpreter, recorded not hidden. Rejected candidates: rt_string_rfind/str_last_index_of — already covered by C-MIG-0024) |

Every `assess` entry must be resolved to a concrete class before Wave-4 work
on it starts (unclassified = critical failure per release gates §18). New
entries append here AND in `c_migration_inventory.sdn`; the SDN file is the
authority.

## Pointer: dispatch-dead audit (goal 2/6, 2026-08-18)

See `doc/08_tracking/c_migration/dispatch_dead_c_audit_2026-08-18.md` — full
sweep of 1458 owned `rt_*` C definitions vs. 1901 registered in
`interpreter_extern/*.rs`: 710 unregistered from the interpreter's dispatch,
of which 250 are native_lane_called (native/AOT codegen or `.spl extern fn`),
93 rust_seed_called, 344 c_internal, and **23 DEAD** (deletion candidates,
each needing one non-grep follow-up check, none deleted). All 8 symbols named
in the originating finding (`rt_string_find`, `rt_string_replace`,
`rt_wire_to_hex`, `rt_hex_to_wire`, string-case family) are live in the
native/AOT lane except `rt_string_replace_first` (registered in the codegen
`RuntimeFuncSpec` table but never emitted/called — linkable but unused).
