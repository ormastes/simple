# rt_* provider classification — 2026-08-28 (gate-lane roots-widening adjudication)

Owner: gate lane (`scripts/check/check-no-direct-rt.shs` roots-widening task).

## Ruling: allowlisted as providers

- `src/lib/common/time_utils.spl` — wraps the clock/time syscall rt_* primitives.
  No deeper Simple layer exists beneath a raw time syscall; genuine runtime
  boundary, same class as the loader mmap/ptr entries already in the
  allowlist.
- `src/lib/common/binary_io.spl` — wraps raw binary byte I/O rt_* primitives.
  Same boundary criterion.
- `src/lib/nogc_sync_mut/mem/dump.spl` — thin typed wrappers over rt_heap_*
  introspection externs, one file, by-kind dump helpers. Flagged by the
  compiler migration lane as provider-shaped (not a product call site to
  migrate).

## Confirmed pre-existing (no change needed)

- `suffix:_sffi.spl` — already in `scripts/check/no_direct_rt_allowlist.txt`
  (suffix match, path-independent). The 2026-08-28 `--roots` widening adds
  `examples/`, `tools/`, `scripts/`, `test/` as scan roots; because this rule
  is a filename-suffix match rather than a path-prefix match, any `*_sffi.spl`
  file under the new roots is already covered without an allowlist edit.

None of these three additions were verified via `--generate-baseline` — that
stays for a deliberate baseline update by whoever owns the ratchet threshold
next.

## Follow-up ruling batch 2 (2026-08-28) — lib-lane residual-scope categories

Source: `$SCRATCHPAD/rt_lanes/lib/REPORT.md` residual-scope section.
Owner: gate lane.

### (a) Already-typed wrapper modules outside ffi/sffi/

Decision: **allowlist in place**, do not relocate. Each file already
declares its own `rt_*` extern once and wraps it in a typed fn/class —
structurally a provider file, just not physically under `ffi/`/`sffi/`.
Relocating them needs a cross-tree import-path audit (every absolute and
relative importer across `src/` and `test/`) that risks breaking working
imports for a purely cosmetic move — explicitly deferred, not attempted.

Allowlisted: `nogc_sync_mut/atomic.spl`, `nogc_sync_mut/concurrent/`,
`nogc_sync_mut/rt_hal/`, and the nine `nogc_sync_mut/io/*_ops.spl` files the
lib lane confirmed are 1:1 wrappers (`stderr_ops.spl`, `env_ops.spl`,
`time_ops.spl`, `file_ops.spl`, `dir_ops.spl`, `process_ops.spl`,
`sysinfo_ops.spl`, `volatile_ops.spl`, `debug_stubs.spl`,
`tls_common_hooks.spl`). Listed as explicit per-file entries, not a
`suffix:_ops.spl` glob — repo-wide `*_ops.spl` (114 files) includes plenty
of ordinary product code (JSON/text/tensor/compiler-backend ops) that is
NOT a boundary wrapper, so a blanket suffix would have been unsafe.

### (b) Boundary-category rulings

GENUINE PROVIDERS (allowlisted, directory- or file-scoped):
- GPU/graphics backend dispatch not already covered by the pre-existing
  `nogc_sync_mut/gpu/` and `.../engine/audio/` entries:
  `engine/render/`, `engine/physics/backend_gpu/`, `gpu_driver/`,
  `gpu_runtime/`, `gpu_profile/`, `io/window_winit.spl`,
  `io/simple_glfw.spl`, `io/simple_sdl3.spl`, `io/metal_ptr.spl`,
  `desktop/display.spl`. Same class as the existing vulkan/metal sffi
  entries: vendor windowing/driver ABI, no pure-Simple replacement.
- ML/tensor: `nogc_sync_mut/cuda/` (the async-side twin
  `nogc_async_mut/cuda/` was already allowlisted; sync-side was a gap).
  `linalg/*` needed no change — already covered by the pre-existing
  `nogc_sync_mut/linalg/` entry.
- JIT codegen: `nogc_sync_mut/jit/` — codegen-emitted symbol names, rule-3
  boundary (same reasoning as the loader `smf_mmap_native.spl` entries).
- Baremetal: `nogc_sync_mut/baremetal/` — device config/terminal/transport
  primitives, rule-3 boundary, same class as the existing
  `nogc_async_mut_noalloc/log/` baremetal-log entry.
- Debug/remote protocol: `debug/remote/`, `debug/native_agent.spl`,
  `debug/smf_agent.spl` — process-level debug primitives (ptrace, DWARF
  unwinding consumption, ST-Link/OpenOCD wire protocol). Scoped narrowly:
  the directory grant is `debug/remote/` only, not all of `debug/`.

PRODUCT CODE (left forbidden, NOT allowlisted — future migration targets):
- `debug/interpreter_backend.spl`, `debug/formats/dsym_resolver.spl` —
  dispatch/parsing logic layered on top of a primitive, not the primitive
  itself; deliberately excluded from the `debug/` grant above.
- Database core (`database/{core,mod,atomic,todo,checker,
  nosql_offload}.spl`, `database/server/capability.spl`,
  `database/sql/statement.spl`, `database/vector/distance.spl`) — this is
  the embedded-DB engine layer (see MEMORY: "Three kinds of Simple DB
  naming"), storage/query logic that CALLS a raw primitive, not a boundary
  itself. Ruled NOT a provider; should route through a typed
  `std.database` wrapper like other product code, not be exempted.

No `--generate-baseline` was run for this batch either.
