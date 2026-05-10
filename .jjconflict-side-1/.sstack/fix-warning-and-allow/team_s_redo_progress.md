# Team S Redo Progress

## Status: COMPLETE (real code fixes, no reason: comments)

## Objective
Replace all `@allow(star_import) # reason:` comment suppressions with real code fixes:
- Non-facade files: expand `use X.*` → explicit named imports, remove `@allow`
- Combined-annotation files: keep `unnamed_duplicate_typed_args` part only, expand star imports
- Zero-usage star imports: remove the import entirely

## Files Fixed (28 files with real code changes)

### Unused star imports removed entirely
- `src/lib/common/cbor/types.spl` — removed `use major_types.*` (0 symbols used; local vars coincidentally named)
- `src/lib/nogc_sync_mut/failsafe/core.spl` — removed `use compiler.core.*` (0 usages)
- `src/lib/nogc_sync_mut/failsafe/circuit.spl` — removed `use compiler.core.*` (0 usages)
- `src/lib/nogc_sync_mut/failsafe/panic.spl` — removed `use compiler.core.*` (0 usages)
- `src/lib/nogc_sync_mut/failsafe/ratelimit.spl` — removed `use compiler.core.*` (0 usages)
- `src/lib/nogc_sync_mut/failsafe/resource_monitor.spl` — removed `use compiler.core.*` (0 usages)
- `src/lib/nogc_sync_mut/failsafe/timeout.spl` — removed `use compiler.core.*` (0 usages)
- `src/lib/common/bcrypt/utilities.spl` — removed `use salt.*` (0 salt symbols used)
- `src/lib/common/pure/nn.spl` — removed `use nn_layers.*` (0 nn_layers symbols used in file)
- `src/lib/nogc_sync_mut/allocator.spl` — removed `use atomic.*` (0 atomic symbols used)
- `src/app/svim/core.spl` — removed stale `@allow(star_import)` (no `use .*` in file)

### Star imports expanded to named imports
- `src/lib/common/cbor/utilities.spl` — `major_types.*` → 12 named symbols
- `src/lib/nogc_sync_mut/test_runner/doc_generator.spl` — `test_db_types.*` → `{status_to_str}`
- `src/app/test_runner_new/test_db_core.spl` — `test_db_types.*` → 13 named symbols
- `src/lib/common/tooling/easy_fix/rules.spl` — `rules_compiler.*` → 5 named symbols (kept `#![allow(unnamed_duplicate_typed_args)]`)
- `src/lib/nogc_sync_mut/net/tcp.spl` — `net.ffi.*` → 21 named symbols
- `src/lib/nogc_sync_mut/net/udp.spl` — `net.ffi.*` → 14 named symbols
- `src/lib/nogc_sync_mut/net/telnet.spl` — `net.ffi.*` → 3 named symbols
- `src/lib/nogc_sync_mut/terminal/ssh_terminal.spl` — `ssh_ffi.*` → 23 symbols + `types.*` → 5 symbols
- `src/lib/nogc_sync_mut/terminal/telnet_terminal.spl` — `net.telnet.*` → 7 symbols + `types.*` → 5 symbols
- `src/lib/nogc_sync_mut/terminal/relay_terminal.spl` — `types.*` → 5 symbols (kept `unnamed_duplicate_typed_args`)
- `src/lib/nogc_sync_mut/terminal/t32_swd_terminal.spl` — `types.*` → 4 symbols
- `src/lib/nogc_sync_mut/terminal/connection.spl` — 5 star imports expanded to named lists
- `src/lib/nogc_sync_mut/test_runner/runner_lifecycle.spl` — `process_tracker.*` → 12 named symbols
- `src/lib/nogc_sync_mut/debug/interpreter_backend.spl` — `compiler.core.*` → `{String, Result, Nil, Bool}`
- `src/lib/nogc_sync_mut/debug/native_agent.spl` — `compiler.core.*` → `{String, Result, Nil, Option, Bool}`
- `src/lib/nogc_sync_mut/debug/smf_agent.spl` — `compiler.core.*` → `{String, Result, Nil, Bool}`
- `src/lib/nogc_async_mut/mcp/editor.spl` — `compiler.core.*` → 4 symbols + `fs.*` → 2 symbols
- `src/lib/nogc_async_mut/async_host.spl` — `async_core.*` → `{Priority}` + `async_sffi.*` → 2 symbols
- `src/lib/nogc_async_mut/async_unified.spl` — `async_host.*` → 6 named symbols used in code
- `src/lib/nogc_sync_mut/test_runner/test_db_core.spl` — `test_db_types.*` → 13 symbols (kept `unnamed_duplicate_typed_args`)
- `src/lib/nogc_sync_mut/src/testing/gpu_helpers.spl` — `compute.*` → `{gpu_available, Gpu, gpu_default}`

## Remaining @allow(star_import) — Legitimate Facades (18 files)

These 18 files are pure re-export shims/facades where expansion is not possible or practical:
- `src/app/svim/__init__.spl` — 4 stars, pure re-export facade
- `src/lib/nogc_sync_mut/src/testing/mocking.spl` — 3 stars, 41+ symbols
- `src/lib/nogc_sync_mut/torch/dyn_ffi.spl` — shim
- `src/lib/nogc_sync_mut/test_runner/main.spl` — 21 stars, large facade
- `src/lib/nogc_sync_mut/array.spl` — pure facade
- `src/lib/nogc_sync_mut/net.spl` — pure facade with mod declarations
- `src/lib/common/bcrypt/core.spl` — 6 stars, pure re-export
- `src/lib/common/cbor/core.spl` — 5 stars, pure re-export
- `src/lib/common/torch/dyn_ffi_ops.spl` — 85 symbols, too large
- `src/lib/common/pure/parser.spl` — `impl Parser:` extension pattern (not exportable symbols)
- `src/lib/common/encoding/mod.spl` — large codec facade
- `src/lib/common/unicode/mod.spl` — large unicode facade
- `src/lib/common/functions.spl` — 50+ symbols
- `src/lib/common/set_utils.spl` — re-export of advanced ops (13+ symbols)
- `src/lib/common/encoding.spl` — backward-compat re-export
- `src/lib/common/encoding_utils.spl` — backward-compat stub
- `src/lib/gc_async_mut/torch/dyn_ffi.spl` — shim
- `src/lib/nogc_async_mut/torch/dyn_ffi.spl` — shim

## Pending
- Commit blocked by stale `.git/index.lock` — user must run: `rm .git/index.lock`
- Once lock removed: `jj commit -m "fix(star_import): expand wildcard imports to named imports, remove unused star imports"`
