# JIT runtime-symbol manifest audit — closing the silent de-JIT class

Date: 2026-07-28. Follow-up to `5c75a1bbce0` (rt_index_of).
Landed: `83e8daa181f`, `89f8e709630`, `ddff6e25b0e` on `main`.

NOT to be added to git.

## Method

`runtime/build.rs` is the only thing that turns the hand-maintained manifest
(`RUNTIME_SYMBOL_NAMES`) into the JIT table. Rather than re-deriving its
behaviour, its helper functions were extracted **verbatim** into a standalone
binary and replayed over the manifest and runtime sources.

Fidelity check: the replay reports **1520 table entries** on `origin/main`,
independently reproducing the exact count `5c75a1bbce0` recorded after its fix.

## Key structural finding (PROVED)

`build.rs` emits a table entry only for `manifest ∩ defined`, and it discovers
`defined` by a **purely textual scan that ignores `cfg`**. Two consequences:

1. Listing an undefined symbol is a silent no-op, not an error.
2. Listing a symbol whose definition disappears under the default feature set
   produces an unconditional `extern` declaration and address-of in the
   generated table → **hard link error**. This is why bulk-adding is wrong.

The manifest already honours this invariant: **0 of its 1520 registered entries
come from a `cfg`-gated module** (0 of 65 `gpu_vulkan` symbols, 0 of 46 monoio
symbols), while 75 `rt_vulkan_` and 31 `rt_cuda_` from *ungated* modules are
registered. The rule below is therefore the tree's existing rule, not a new one.

## Classification

Raw `rt_*` string literals under `compiler/src/codegen` absent from the
manifest: **369**. Most are prefix fragments (`"rt_array_"`, `"rt_actor_"`) used
for `starts_with` comparisons, not call names — they can never match a real
definition, so they are noise, not "codegen calling a nonexistent function".

| Class | Count | Verdict |
|---|---|---|
| Emitted + defined + always linkable + missing | **24** | **live bugs — ADDED** |
| Emitted + defined but module is `cfg`-gated | 48 | correctly absent; adding breaks the build |
| Emitted, no definition found (prefix fragments etc.) | 296 | noise, not defects |
| Emitted + defined, no definition site resolvable | 1 | `rt_win32_window_new` — see below |
| In manifest but never emitted by codegen | 740 | dead, left alone |

### Added — batch 1 (12)
`rt_array_all`, `rt_array_any`, `rt_array_filter`, `rt_array_find` (all
unconditional in `value/collections.rs`), `rt_str_hash`, `rt_exec`,
`rt_write_file`, `rt_value_as_int`, `rt_sleep_ms`, `rt_neighbor_load`,
`rt_cuda_launch_kernel_name`, `rt_cuda_module_load_data_bytes`
(the two `rt_cuda_` use complementary stubs in the ungated `cuda_runtime.rs`).

### Added — batch 2 (12)
The 12 `rt_vulkan_*` graphics entry points in the **ungated**
`vulkan_graphics_runtime_*` modules, each with complementary
`cfg(feature="vulkan")` / `cfg(not(...))` definitions. 75 siblings already
registered.

### Correctly absent — do NOT add (48)
- **44 `rt_vk_*`** — `value/gpu_vulkan` is `#[cfg(feature = "vulkan")]`; vulkan
  is not a default feature. Absence is correct in every shipping configuration.
  If vulkan is ever turned on, these become de-JIT hazards; the fix then is a
  conditional manifest, which the current single-list format does not support.
- **4 `rt_monoio_*`** — `monoio_direct` / `value/monoio_future` are
  `#[cfg(feature = "monoio-direct")]`. Same reasoning.

### `rt_win32_window_new`
Emitted at `codegen/instr/calls.rs:2496`; no definition site in
`runtime/src`. It matched only via the C scan of `hosted_win32.c`, which
`build.rs` **skips** on Windows and under `native-all-provider`. Not added.
Filed here as a separate, weaker concern: an emitted name with no
platform-independent definition.

## Two defects found incidentally

1. **Phantom manifest entries.** `build.rs` takes the first quoted token on
   *every* line in the list, comments included. A pre-existing comment
   containing `"Undefined symbol: rt_any_add"` was contributing a bogus symbol
   name. Harmless in the table (undefined names are filtered) but wrong. Fixed,
   and the new check fails on recurrence. I hit this trap myself when writing
   the batch-2 comment.
2. **`value/simd.rs` has CRLF line endings.** Rust's `str::lines()` + `trim()`
   strips `\r`, so `build.rs` is unaffected — but any `awk`/shell tooling that
   does not strip `\r` silently under-reports symbols in that file. This
   initially hid `rt_neighbor_load` from my own check.

## Class closure

`scripts/check/check-jit-runtime-symbol-manifest.shs` fails when codegen emits
an `rt_*` symbol that is always linkable and absent from the manifest, and on
phantom comment entries. Verified both directions: **24 missing + 1 phantom,
exit 1** before the fixes; **0, exit 0** after.

It deliberately does not demand every emitted name — that would break the build
for the `cfg`-gated families. Documented limits: definition discovery mirrors
`build.rs`'s exact `no_mangle`/`export_name` forms; emission detection is
string-literal based. Both make it conservative — it can miss a divergence, but
every failure it reports is real.

## Verification status

- **PROVED**: manifest line → generated table entry, per batch. Table moves
  1520 → 1532 → 1544, exactly 24 entries gained, **zero entries lost**, via a
  verbatim replay of `build.rs` whose baseline reproduces the count from
  `5c75a1bbce0`.
- **PROVED**: the tested tree is byte-identical to what landed
  (manifest blob `eeb4766a637b43b2da7e340aab71dc120be4f237`).
- **NOT MEASURED**: end-to-end JIT-versus-interpreter runtime values. That needs
  a bootstrap redeploy, which was not available during this session (load ~60).
  No timing claim is made. The resolution chain is proven; the speedup is not.
