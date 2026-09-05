# Census: `rt_*` extern names reachable from neither the static dispatch table nor the runtime `.so` exports

Status: CLOSED (not reproducible)
Status re-verified 2026-08-17 by source inspection (triage shard 02).
Scope: enumeration only — **no product code changed by this doc.** Feeds R1/R2/R3 and any
future lane with a concrete work-list instead of a bare headcount.
## 1. What was measured, and against what

Base commit: `ea198ba3e609a591d470c7a143b7f96b513b4adb` (HEAD at measurement time,
2026-08-05). **Caveat:** `src/compiler_rust/compiler/src/interpreter_extern/mod.rs` carried
local uncommitted edits at measurement time from a parallel in-flight session — confirmed by
`git diff --stat` to be scoped entirely to `rt_vulkan_*` arms (adding `pub mod vulkan;` /
`pub mod capability_gap;`, consolidating `rt_vulkan_*` inserts). `rt_vulkan_*` is explicitly
out of scope for every lane in the parent plan ("Exclusion" note at the top of the plan doc),
so this does not contaminate any bucket counted here — `rt_vk_` (a different prefix) was
independently confirmed to have zero `mod.rs` string-literal hits either way.

Three sets, built with `/usr/bin/grep` (ugrep is the shell default here; every pattern below
was pinned to `/usr/bin/grep` and anchored — see §5 for the FP this caught):

1. **DECLARED** — every `rt_*` name with a real `extern fn NAME(` declaration line under
   `src/lib/**/*.spl` and `src/app/**/*.spl` (vendored trees excluded; none contain `.spl`
   anyway). Command:
   ```
   /usr/bin/grep -rhnE '^[[:space:]]*(pub[[:space:]]+)?extern[[:space:]]+fn[[:space:]]+rt_[a-z0-9_]+\(' \
     src/lib src/app --include='*.spl' \
     | /usr/bin/grep -oE 'rt_[a-z0-9_]+\(' | tr -d '(' | sort -u
   ```
   **2,271 names.**

2. **STATIC_TABLE** — every `"rt_..."` string literal anywhere under
   `src/compiler_rust/compiler/src/interpreter_extern/*.rs` (covers `mod.rs`'s dispatch-table
   inserts, `sdl2.rs`'s typed table, and every other family module's direct registrations).
   ```
   /usr/bin/grep -rhoE '"rt_[a-z0-9_]+"' src/compiler_rust/compiler/src/interpreter_extern --include='*.rs' \
     | tr -d '"' | sort -u
   ```
   **1,611 names.**

3. **SO_EXPORTS** — every `rt_*` symbol in the dynamic symbol table of the freshest built
   runtime shared object, `build/bootstrap-adhoc-20260805-user/stage3/x86_64-unknown-linux-gnu/
   stage2-runtime-authority/libsimple_runtime.so` (built 2026-08-05 06:28, i.e. same-day, ahead
   of the in-flight `mod.rs` edit at 06:42). `nm -D --defined-only`, filtered to `rt_*`.
   **1,561 names.**

**UNREACHABLE = DECLARED − STATIC_TABLE − SO_EXPORTS = 1,003 names.**
## 2. Discrepancy with the ~509 figure quoted in the dispatching brief

No document in the repo could be located that records how the ~509 number was originally
produced (searched `doc/03_plan/runtime/native_binding/`, `doc/04_architecture/runtime/
native_library_binding_survey.md`, and `doc/08_tracking/bug/*509*` — none contain a
methodology for that specific figure). Rather than force-fit the regenerated set to match an
unreproducible number, this doc reports the **measured** count: **1,003**, roughly 2x the
quoted figure. Two candidate explanations were checked and ruled out: (a) a fuller runtime
build with GUI backends exporting more symbols — checked two other `.so` builds
(`build/redeploy_runtime/libsimple_runtime.so`, `build/fable_s2/runtime/libsimple_runtime.so`);
neither exports any `rt_glfw_/rt_sdl3_/rt_opengl_/rt_oneapi_` symbol either, so that is not it;
(b) the STATIC_TABLE set undercounting due to the in-flight `mod.rs` edit — ruled out in §1
(scoped to `rt_vulkan_*` only, zero effect on any bucket below). The gap is left as an open
question rather than papered over.
## 3. Bucket definitions

- **(a) source-list-absent** — a real `.c` definition exists under `src/runtime/`, but the
  defining file is not in the default host build's source array (`sources = [...]` at
  `src/compiler/70.backend/backend/runtime_compiler.spl:268`, plus `runtime_dynload` counted in
  since `include_dynload` defaults `true`). This is the exact SDL2 root-cause shape: real code,
  just not linked in.
- **(b) has native definitions but not registered** — a real `.c` definition exists AND its
  file IS in the default source array, but the name has no dispatch-table entry (M1 shape:
  sdl2/glfw/sdl3/opengl/oneapi).
- **(c) zero native definitions anywhere** — no `.c` definition anywhere under `src/runtime/`
  (headers included in the search; none found there either). R3's capability-gap territory
  (webgpu/vk/gui/lyon/gamepad), plus others discovered here.
- **(d) genuinely orphaned/dead** — zero call sites outside the name's own declaration line(s)
  anywhere under `src/lib`, `src/app`, `test` (a per-name occurrence count minus its own
  declaration-line count, both counted with the same anchored pattern as §1). Checked
  independently of (a)/(b)/(c): a dead name is bucketed (d) even if it also has a native
  definition, since the priority question for a work-list is "does anything reach this at
  all", not "could it theoretically be wired".

Priority order when a name qualifies for more than one bucket: **(d) first** (dead beats
everything — a name nothing calls doesn't need a registration decision), then (a)/(b)/(c) by
native-definition status.
## 4. Result

| bucket | count | % of 1003 |
|---|---|---|
| (a) source-list-absent | 51 | 5.1% |
| (b) native def, unregistered | 191 | 19.0% |
| (c) zero native def anywhere | 576 | 57.4% |
| (d) dead / orphaned | 185 | 18.4% |
| **total** | **1003** | 100% |

### Worst instances per bucket

**(a) source-list-absent** — dominated by `rt_audio_*` (31/51 names; `runtime_audio.c`
has full implementations, `runtime_audio` is simply absent from the `sources` array at
`runtime_compiler.spl:268` — the audio backend is compiled and linked nowhere in the default
host build). Highest-traffic examples (live `.spl` call sites, declaration line excluded):

- `rt_audio_set_volume` — 10 call sites — native def NOT in default source list: runtime_audio
- `rt_audio_play` — 8 call sites — native def NOT in default source list: runtime_audio
- `rt_audio_set_sound_position` — 7 call sites — native def NOT in default source list: runtime_audio
- `rt_audio_set_listener_position` — 6 call sites — native def NOT in default source list: runtime_audio
- `rt_audio_set_spatialization_enabled` — 6 call sites — native def NOT in default source list: runtime_audio
- `rt_audio_unload_sound` — 6 call sites — native def NOT in default source list: runtime_audio
- `rt_audio_load_sound` — 5 call sites — native def NOT in default source list: runtime_audio
- `rt_audio_set_master_volume` — 5 call sites — native def NOT in default source list: runtime_audio

**(b) native def, unregistered** — dominated by the M1/M2 families from R1/R2
(`rt_glfw_` 39, `rt_sdl3_` 22, `rt_opengl_` 17, `rt_oneapi_` 13 — all confirmed present in
`runtime_native.c`/`runtime_glfw.c`/`runtime_sdl3.c`, all confirmed in the default `sources`
array, **and all confirmed absent from the sampled `.so`'s dynamic exports** — an open question
for R1/R2, not resolved here). Also non-GUI examples with real traffic:

- `rt_process_write_stdin` — 18 call sites — native def in default-build file(s): runtime_process
- `rt_process_read_stdout` — 15 call sites — native def in default-build file(s): runtime_process
- `rt_process_spawn_piped` — 14 call sites — native def in default-build file(s): runtime_process
- `rt_io_udp_bind` — 11 call sites — native def in default-build file(s): runtime_native
- `rt_process_is_alive` — 9 call sites — native def in default-build file(s): runtime_process
- `rt_wire_to_hex` — 9 call sites — native def in default-build file(s): runtime
- `rt_io_udp_close` — 8 call sites — native def in default-build file(s): runtime_native
- `rt_io_udp_recv_from` — 6 call sites — native def in default-build file(s): runtime_native

**(c) zero native definitions anywhere** — the largest bucket (576/1003, 57%).
`rt_torch_*` alone is 90 names (heaviest single family with zero native side, C or Rust).
`rt_lyon_` (49) and `rt_gamepad_` (20) match the plan's prediction exactly (R3 territory).
`rt_vk_` (25, distinct from the excluded `rt_vulkan_` prefix) also has zero definitions.
The most concerning finding in this bucket is **`rt_shell_exec`** (54 live call sites across
the terminal/power stack — `src/lib/nogc_sync_mut/terminal/power/host_power.spl` and
`relay_power.spl`, among others) and its sibling **`rt_shell_exit_code`** (34 call sites):
both are declared, called from real production code paths, and have **no implementation at
all** — not in any `src/runtime/*.c`, not as a Rust match arm in `interpreter_extern/*.rs`.
This is not a GPU/GUI capability gap; it is a plain shell-exec primitive with real callers and
no backing code anywhere. Full top-8 by traffic:

- `rt_shell_exec` — 54 call sites — zero native (.c) definitions anywhere
- `rt_shell_exit_code` — 34 call sites — zero native (.c) definitions anywhere
- `rt_process_run_capture` — 22 call sites — zero native (.c) definitions anywhere
- `rt_torch_torchtensor_mean_dim` — 18 call sites — zero native (.c) definitions anywhere
- `rt_cuda_memcpy_h2d` — 17 call sites — zero native (.c) definitions anywhere
- `rt_torch_torchtensor_div` — 17 call sites — zero native (.c) definitions anywhere
- `rt_torch_tensor_zeros` — 16 call sites — zero native (.c) definitions anywhere
- `rt_torch_torchtensor_sqrt` — 16 call sites — zero native (.c) definitions anywhere

**(d) genuinely orphaned/dead** — 185 names, of which **75 (40.5%) trace to a single
directory**: `src/app/ffi_gen.specs/*.spl`. That directory holds ~30 files of bulk-generated
FFI *spec* stubs (`gc.spl`, `gc_full.spl`, `cargo.spl`, `coverage.spl`, `crypto_mod.spl`, ...)
— each declares a family's full theoretical extern surface but most of it is never called from
anywhere else in the tree. `rt_gc_*` alone is 61 of the 185 dead names, and `gc.spl` +
`gc_full.spl` account for the bulk of that. This is a distinct failure mode from (a)/(b)/(c):
it is not a registration gap at all, it is speculative/generated interface surface that was
never wired to a real caller. Worth a decision (delete vs. keep as documentation) rather than a
registration lane. Sample:

- `rt_aes_gcm_decrypt_hex` — dead: 0 non-declaration call sites
- `rt_aes_gcm_encrypt_hex` — dead: 0 non-declaration call sites
- `rt_audio_sdl2_queued_bytes` — dead: 0 non-declaration call sites
- `rt_audio_sdl2_submitted_frames` — dead: 0 non-declaration call sites
- `rt_audio_sdl2_underrun_count` — dead: 0 non-declaration call sites
- `rt_bigint_mod_exp` — dead: 0 non-declaration call sites
- `rt_cuda3d_apply_bloom` — dead: 0 non-declaration call sites
- `rt_cuda3d_apply_fog` — dead: 0 non-declaration call sites

## 5. Measured false-positive rate

**Extraction stage** — a first-pass naive pattern (`grep -rhoE 'fn[[:space:]]+rt_[a-z0-9_]+'`,
no line-anchor) over the same tree returned 2,286 names. Diffing against the anchored v2
pattern (§1.1) showed **15 false positives (15/2,286 = 0.66%)**, all from lines that are not
real declarations: doc-comment prose (`# ... extern fn rt_cuda_*` — the naive pattern captured

the truncated `rt_cuda_` before the un-matched `*`; same shape for `rt_dwarf_`, `rt_gc_`,
`rt_pool_`, `rt_ptrace_`, `rt_volatile_`), a commented-out declaration
(`# extern fn rt_file_write(...) # Disabled - not in runtime extern registry`), a string

literal inside a test-code generator (`"extern fn rt_bdd_clear_state()\n" + ...`), and a
comment inside an audit tool describing the pattern it greps for
(`# Pattern: extern fn rt_name(`). All 15 were hand-checked individually (listed in full below)

and confirmed non-declarations before being dropped; the anchored pattern
(`^[[:space:]]*(pub[[:space:]]+)?extern[[:space:]]+fn[[:space:]]+rt_[a-z0-9_]+\(`) used for the
actual census (§1) does not match any of them.

Dropped 15: `rt_bdd_clear_state, rt_bdd_executed_count, rt_bdd_expect_truthy,
rt_bdd_format_results, rt_clock_now_ms, rt_cuda_, rt_dwarf_, rt_file_write, rt_gc_, rt_name,
rt_new_function, rt_pool_, rt_ptrace_, rt_signal_handler_set, rt_volatile_`.

**Classification stage** — a stratified hand-verified sample of **33 names** (≥20 required by
the gate), 6-8 drawn from each of the four buckets plus 4 extra targeted checks (multi-file
native-def cases, the `rt_shell_exec`/`rt_engine2d_pack_args_8` worst instances, and the
`ffi_gen.specs` concentration in bucket d). Each was independently re-verified against the
repo (grep for the actual `.c` definition or actual call site, not re-running the census
script) rather than trusting the script's own output. **Result: 33/33 correct — 0 measured
misclassifications (0%).** No bucket showed a miss in this sample; the two near-misses caught
during verification were both benign — `rt_log_target_semihost_write_bytes` (bucket a)
resolved to a real but nonstandard-location file
(`src/runtime/startup/baremetal/runtime_log.c`, a baremetal-only startup path outside the
top-level `src/runtime/*.c` convention) and `rt_atexit_check`/`rt_dma_*` (bucket b) resolved to
multiple defining files, which the classifier already handles correctly (any defining file in
the default source array is sufficient for bucket b).

### Sabotage check (per the gate)

Seeded the scanner input with `rt_sdl2_init`, a name known to be registered (`sdl2.rs`'s typed
table, the SDL2 precedent this whole campaign is modeled on). Confirmed **present** in
STATIC_TABLE (`"rt_sdl2_init"` literal exists in `interpreter_extern/*.rs`) and confirmed
**absent** from the final UNREACHABLE/classified set. Passed both before and after the
extraction-pattern fix in §5.

## 6. Spot-check commands (one per bucket)

```bash
# bucket (a) — e.g. rt_audio_play: has a .c def, file not in the default sources array

/usr/bin/grep -n 'rt_audio_play\b' src/runtime/runtime_audio.c
/usr/bin/grep -n 'runtime_audio' src/compiler/70.backend/backend/runtime_compiler.spl   # no hit

# bucket (b) — e.g. rt_process_write_stdin: has a .c def, file IS in the sources array, no dispatch entry

/usr/bin/grep -n 'rt_process_write_stdin' src/runtime/runtime_process.c
/usr/bin/grep -n '"rt_process_write_stdin"' src/compiler_rust/compiler/src/interpreter_extern/*.rs  # no hit

# bucket (c) — e.g. rt_shell_exec: no .c def anywhere, no Rust match arm anywhere

/usr/bin/grep -rn 'rt_shell_exec' src/runtime --include='*.c' --include='*.h'                  # no hit

/usr/bin/grep -n '"rt_shell_exec"' src/compiler_rust/compiler/src/interpreter_extern/*.rs      # no hit

# bucket (d) — e.g. rt_gc_allocate: only its own declaration line, zero real callers

/usr/bin/grep -rn 'rt_gc_allocate' src/lib src/app test --include='*.spl'
```

## 7. Reproduction

All intermediate files were built in a scratch dir and are not checked in (per repo policy —
no report artifacts committed unless requested). To regenerate:

```bash
cd /home/ormastes/dev/pub/simple
# 1. DECLARED

/usr/bin/grep -rhnE '^[[:space:]]*(pub[[:space:]]+)?extern[[:space:]]+fn[[:space:]]+rt_[a-z0-9_]+\(' \
  src/lib src/app --include='*.spl' \
  | /usr/bin/grep -oE 'rt_[a-z0-9_]+\(' | tr -d '(' | sort -u > declared.txt
# 2. STATIC_TABLE

/usr/bin/grep -rhoE '"rt_[a-z0-9_]+"' src/compiler_rust/compiler/src/interpreter_extern --include='*.rs' \
  | tr -d '"' | sort -u > static_table.txt
# 3. SO_EXPORTS (adjust path to the freshest built .so)

nm -D --defined-only build/bootstrap-adhoc-20260805-user/stage3/x86_64-unknown-linux-gnu/\
  stage2-runtime-authority/libsimple_runtime.so | /usr/bin/grep -oE '\brt_[a-z0-9_]+$' | sort -u > so_exports.txt
# 4. UNREACHABLE

comm -23 declared.txt <(sort -u static_table.txt so_exports.txt) > unreachable.txt
```
Bucket classification then joins `unreachable.txt` against (i) a name→defining-.c-file map built
from `/usr/bin/grep -rnoE '^[A-Za-z_][A-Za-z0-9_ *]*\brt_[a-z0-9_]+\s*\(' src/runtime --include='*.c'`
(excluding `vendor/` and `test/`), (ii) the `sources` array at
`src/compiler/70.backend/backend/runtime_compiler.spl:268`, and (iii) a per-name call-site count
from the same anchored declaration pattern applied to `src/lib src/app test`, minus each name's own
declaration-line count.

## Appendix A — bucket (a), source-list-absent, 51 names

```
rt_audio_backend_is_real, rt_audio_backend_name, rt_audio_capture_frame_count,
rt_audio_capture_is_active, rt_audio_capture_start, rt_audio_capture_stop,
rt_audio_get_master_volume, rt_audio_init, rt_audio_is_playing, rt_audio_live_device_count,
rt_audio_live_playback_count, rt_audio_live_source_count, rt_audio_load_sound, rt_audio_pause,
rt_audio_play, rt_audio_play_looped, rt_audio_play_pcm_f32, rt_audio_play_pcm_f64_raw,
rt_audio_resume, rt_audio_set_listener_direction, rt_audio_set_listener_position,
rt_audio_set_listener_world_up, rt_audio_set_master_volume, rt_audio_set_sound_max_distance,
rt_audio_set_sound_min_distance, rt_audio_set_sound_position,
rt_audio_set_spatialization_enabled, rt_audio_set_volume, rt_audio_shutdown, rt_audio_stop,
rt_audio_unload_sound, rt_fb_blit32, rt_fb_fill32, rt_image_channels, rt_image_free,
rt_image_get_pixel, rt_image_height, rt_image_load, rt_image_width,
rt_log_target_device_write_bytes, rt_log_target_semihost_write_bytes, rt_mmio_read_u16,
rt_mmio_read_u32, rt_mmio_read_u8, rt_mmio_write_u16, rt_mmio_write_u32, rt_mmio_write_u8,
rt_simpleos_log_emit, rt_simpleos_log_init, rt_simpleos_log_set_device,
rt_socket_set_nonblocking
```

## Appendix B — bucket (b), native def unregistered, 191 names

```
rt_atexit_check, rt_atexit_install, rt_audio_sdl2_close, rt_audio_sdl2_init,
rt_audio_sdl2_live_device_count, rt_audio_sdl2_queue_pcm_f64_raw,
rt_browser_renderer_sandbox_enter, rt_browser_renderer_spawn_sandboxed, rt_dir_delete,
rt_dma_alloc, rt_dma_cache_line_size, rt_dma_free, rt_dma_phys_of, rt_dma_sync_for_cpu,
rt_dma_sync_for_device, rt_editor_poll_simple_dap_stopped, rt_editor_spawn_simple_dap,
rt_editor_wait_simple_dap_stopped, rt_file_append, rt_font_ascent, rt_font_bitmap_free,
rt_font_bitmap_get_pixel, rt_font_bitmap_height, rt_font_bitmap_width, rt_font_bitmap_xoff,
rt_font_bitmap_yoff, rt_font_free, rt_font_glyph_advance, rt_font_glyph_advance_index,
rt_font_glyph_bitmap, rt_font_glyph_bitmap_index, rt_font_glyph_index, rt_font_line_height,
rt_font_load, rt_font_load_bytes, rt_fork_child_exit, rt_fork_child_setup,
rt_fork_parent_stderr, rt_fork_parent_stdout, rt_fork_parent_wait, rt_glfw_clipboard_get,
rt_glfw_clipboard_set, rt_glfw_content_scale_milli, rt_glfw_create_window,
rt_glfw_destroy_window, rt_glfw_dropped_event_count, rt_glfw_event_action,
rt_glfw_event_dx_milli, rt_glfw_event_dy_milli, rt_glfw_event_height, rt_glfw_event_key,
rt_glfw_event_modifiers, rt_glfw_event_scancode, rt_glfw_event_sequence, rt_glfw_event_text,
rt_glfw_event_timestamp_ns, rt_glfw_event_width, rt_glfw_event_window, rt_glfw_event_x_milli,
rt_glfw_event_y_milli, rt_glfw_focus, rt_glfw_frame_sequence, rt_glfw_framebuffer_height,
rt_glfw_framebuffer_width, rt_glfw_init, rt_glfw_live_window_count, rt_glfw_maximize,
rt_glfw_minimize, rt_glfw_pop_event, rt_glfw_present_argb, rt_glfw_present_argb_words_raw,
rt_glfw_pump_events, rt_glfw_queued_event_count, rt_glfw_restore, rt_glfw_set_visible,
rt_glfw_should_close, rt_glfw_terminate, rt_glfw_window_height, rt_glfw_window_width,
rt_hex_to_wire, rt_http_client_create, rt_http_client_destroy, rt_http_client_request,
rt_http_client_set_timeout, rt_http_download, rt_intel_engine2d_download_pixels,
rt_intel_engine2d_set_args_blit, rt_intel_engine2d_set_args_circle,
rt_intel_engine2d_set_args_clear, rt_intel_engine2d_set_args_gradient,
rt_intel_engine2d_set_args_line, rt_intel_engine2d_set_args_rect,
rt_intel_engine2d_set_args_rounded_rect, rt_intel_engine2d_set_args_triangle,
rt_intel_engine2d_upload_host_buf, rt_intel_engine2d_upload_pixels, rt_io_udp_bind,
rt_io_udp_close, rt_io_udp_connect, rt_io_udp_local_addr, rt_io_udp_recv, rt_io_udp_recv_from,
rt_io_udp_send, rt_io_udp_send_to, rt_io_udp_set_broadcast, rt_io_udp_set_nonblocking,
rt_io_udp_set_read_timeout, rt_oneapi_compile_opencl, rt_oneapi_compile_spirv,
rt_oneapi_create_queue, rt_oneapi_destroy_queue, rt_oneapi_device_count, rt_oneapi_free,
rt_oneapi_get_function, rt_oneapi_init, rt_oneapi_malloc_device, rt_oneapi_memset,
rt_oneapi_queue_wait, rt_oneapi_submit_kernel, rt_oneapi_unload_module, rt_opengl_bind_fbo,
rt_opengl_clear, rt_opengl_clear_scissor, rt_opengl_create_fbo, rt_opengl_destroy,
rt_opengl_destroy_fbo, rt_opengl_draw_circle, rt_opengl_draw_gradient_rect,
rt_opengl_draw_image, rt_opengl_draw_line, rt_opengl_draw_rect, rt_opengl_draw_rounded_rect,
rt_opengl_draw_triangle, rt_opengl_flush, rt_opengl_init, rt_opengl_read_pixels,
rt_opengl_set_scissor, rt_path_extension, rt_path_filename, rt_process_close_piped,
rt_process_is_alive, rt_process_read_stdout, rt_process_spawn_piped, rt_process_write_stdin,
rt_process_write_stdin_some, rt_readline, rt_realloc, rt_rsa_decrypt, rt_sdl3_available,
rt_sdl3_create_window, rt_sdl3_destroy_window, rt_sdl3_event_action, rt_sdl3_event_dx_milli,
rt_sdl3_event_dy_milli, rt_sdl3_event_height, rt_sdl3_event_key, rt_sdl3_event_modifiers,
rt_sdl3_event_scancode, rt_sdl3_event_sequence, rt_sdl3_event_text, rt_sdl3_event_timestamp_ns,
rt_sdl3_event_width, rt_sdl3_event_window, rt_sdl3_event_x_milli, rt_sdl3_event_y_milli,
rt_sdl3_init, rt_sdl3_last_error, rt_sdl3_live_window_count, rt_sdl3_pop_event, rt_sdl3_quit,
rt_sdl_create_window, rt_sdl_destroy_window, rt_sdl_event_key_mod, rt_sdl_event_key_sym,
rt_sdl_event_mouse_x, rt_sdl_event_mouse_y, rt_sdl_event_text, rt_sdl_event_window_data1,
rt_sdl_event_window_data2, rt_sdl_event_window_event_id, rt_sdl_get_window_height,
rt_sdl_get_window_width, rt_sdl_init, rt_sdl_poll_event, rt_sdl_present_rgba, rt_sdl_quit,
rt_shell_output, rt_signal_check, rt_signal_install, rt_sleep_secs, rt_wire_to_hex
```

## Appendix C — bucket (c), zero native definitions anywhere, 576 names

```
rt_audio_add_delay, rt_audio_add_highpass, rt_audio_add_lowpass, rt_audio_add_reverb,
rt_audio_clear_effects, rt_audio_remove_effect, rt_audio_set_pitch, rt_cli_args,
rt_cli_run_ffi_gen, rt_command_output, rt_coverage_path_finalizer, rt_cpu_arch_name,
rt_cpu_count, rt_cpu_has_avx2, rt_cpu_has_avx512, rt_cpu_has_neon, rt_cpu_has_sse42,
rt_cpu_present_pixels, rt_cuda3d_available, rt_cuda3d_init, rt_cuda3d_shutdown,
rt_cuda_alloc_device, rt_cuda_alloc_fb, rt_cuda_cleanup, rt_cuda_clear, rt_cuda_compile_ptx,
rt_cuda_compute_capability, rt_cuda_device_init, rt_cuda_device_memory, rt_cuda_draw_rect,
rt_cuda_get_device, rt_cuda_get_function, rt_cuda_get_last_error, rt_cuda_kernel_get,
rt_cuda_kernel_launch, rt_cuda_memcpy_d2d, rt_cuda_memcpy_d2h, rt_cuda_memcpy_h2d,
rt_cuda_peek_last_error, rt_cuda_primary_ctx_release, rt_cuda_primary_ctx_retain,
rt_cuda_readback, rt_cuda_set_device, rt_cuda_shutdown, rt_cuda_stream_create,
rt_cuda_stream_destroy, rt_cuda_stream_sync, rt_cuda_stream_synchronize, rt_cuda_submit,
rt_cuda_synchronize, rt_cuda_unload_module, rt_debug_clear_breakpoints, rt_debug_clear_globals,
rt_debug_clear_locals, rt_debug_current_column, rt_debug_get_step_mode,
rt_debug_get_step_start_depth, rt_debug_globals, rt_debug_has_breakpoint, rt_debug_is_paused,
rt_debug_pop_frame, rt_debug_push_frame, rt_debug_set_current_location, rt_debug_set_global,
rt_debug_set_local, rt_debug_set_step_start_depth, rt_debug_should_break,
rt_debug_wait_for_continue, rt_decrypt_aes256, rt_deflate_compress, rt_deflate_decompress,
rt_derive_key_pbkdf2, rt_dma_virt_of, rt_dwarf_addr_to_line, rt_dwarf_free,
rt_dwarf_function_at, rt_dwarf_line_to_addr, rt_dwarf_load, rt_dwarf_locals_at,
rt_ecdsa_p384_sign, rt_ecdsa_p384_verify, rt_ecdsa_p521_sign, rt_ecdsa_p521_verify,
rt_editor_start_simple_dap, rt_encrypt_aes256, rt_engine2d_download_pixels,
rt_engine2d_pack_args_4, rt_engine2d_pack_args_8, rt_engine2d_upload_host_buf,
rt_engine2d_upload_pixels, rt_ensure_dir, rt_env_get_home, rt_file_modified,
rt_file_modified_time, rt_file_read, rt_file_set_mode, rt_file_write_bytes_b64,
rt_font_find_table, rt_font_read_i16, rt_font_read_u16, rt_font_read_u32, rt_ftp_append,
rt_ftp_cdup, rt_ftp_connect, rt_ftp_connect_secure, rt_ftp_cwd, rt_ftp_delete,
rt_ftp_disconnect, rt_ftp_get, rt_ftp_get_welcome_msg, rt_ftp_is_connected, rt_ftp_list,
rt_ftp_login, rt_ftp_mdtm, rt_ftp_mkdir, rt_ftp_noop, rt_ftp_put, rt_ftp_pwd, rt_ftp_quit,
rt_ftp_rename, rt_ftp_rmdir, rt_ftp_set_mode_active, rt_ftp_set_mode_passive,
rt_ftp_set_transfer_type_ascii, rt_ftp_set_transfer_type_binary, rt_ftp_size,
rt_gamepad_axis_data, rt_gamepad_button_data, rt_gamepad_button_is_pressed, rt_gamepad_count,
rt_gamepad_event_free, rt_gamepad_event_get_axis, rt_gamepad_event_get_button,
rt_gamepad_event_get_gamepad_id, rt_gamepad_event_get_type, rt_gamepad_event_get_value,
rt_gamepad_get_last_error, rt_gamepad_get_name, rt_gamepad_get_power_info, rt_gamepad_init,
rt_gamepad_is_connected, rt_gamepad_poll_event, rt_gamepad_set_rumble, rt_gamepad_shutdown,
rt_gamepad_stop_rumble, rt_gamepad_update, rt_gc_collect, rt_gc_init, rt_gc_malloc,
rt_generate_key, rt_generate_key_hex, rt_ghdl_verify_return_zero_contract,
rt_ghdl_verify_vhdl_constraints, rt_gui_present_html, rt_gzip_compress, rt_gzip_compress_file,
rt_gzip_decompress, rt_gzip_decompress_file, rt_hash_blake3, rt_hash_sha256, rt_hash_sha3_256,
rt_hash_sha512, rt_hmac_sha256, rt_hmac_sha512, rt_hook_add_breakpoint, rt_hook_continue,
rt_hook_disable_debugging, rt_hook_enable_debugging, rt_hook_evaluate_condition,
rt_hook_evaluate_expression, rt_hook_get_call_depth, rt_hook_get_stack_frames,
rt_hook_get_variables, rt_hook_pause, rt_hook_remove_breakpoint, rt_hook_set_breakpoint_enabled,
rt_hook_step, rt_hook_terminate, rt_http_client_set_header, rt_http_delete, rt_http_head,
rt_http_patch, rt_http_post, rt_http_put, rt_http_server_create, rt_http_server_destroy,
rt_http_server_route, rt_http_server_start, rt_http_server_static, rt_http_server_stop,
rt_http_upload, rt_http_url_decode, rt_http_url_encode, rt_init_signal_handlers,
rt_intel3d_available, rt_intel3d_init, rt_intel3d_shutdown, rt_intel_command_list_create,
rt_intel_device_count, rt_intel_driver_count, rt_intel_init, rt_intel_is_available,
rt_intel_kernel_create, rt_intel_launch_kernel, rt_intel_mem_alloc, rt_intel_mem_free,
rt_intel_shutdown, rt_list_dir_recursive, rt_lyon_fill_tessellate,
rt_lyon_fill_tessellate_with_rule, rt_lyon_fill_tessellation_free,
rt_lyon_fill_tessellation_get_indices, rt_lyon_fill_tessellation_get_vertices,
rt_lyon_fill_tessellation_index_count, rt_lyon_fill_tessellation_vertex_count,
rt_lyon_get_last_error, rt_lyon_index_buffer_free, rt_lyon_index_buffer_get,
rt_lyon_index_buffer_size, rt_lyon_index_buffer_to_array, rt_lyon_path_builder_arc_to,
rt_lyon_path_builder_begin, rt_lyon_path_builder_build, rt_lyon_path_builder_close,
rt_lyon_path_builder_cubic_bezier_to, rt_lyon_path_builder_free, rt_lyon_path_builder_line_to,
rt_lyon_path_builder_new, rt_lyon_path_builder_quadratic_bezier_to, rt_lyon_path_circle,
rt_lyon_path_contains_point, rt_lyon_path_ellipse, rt_lyon_path_free, rt_lyon_path_get_bounds,
rt_lyon_path_polygon, rt_lyon_path_rectangle, rt_lyon_path_rounded_rectangle, rt_lyon_path_star,
rt_lyon_path_transform, rt_lyon_stroke_tessellate, rt_lyon_stroke_tessellate_with_options,
rt_lyon_stroke_tessellation_free, rt_lyon_stroke_tessellation_get_indices,
rt_lyon_stroke_tessellation_get_vertices, rt_lyon_stroke_tessellation_index_count,
rt_lyon_stroke_tessellation_vertex_count, rt_lyon_transform_free, rt_lyon_transform_identity,
rt_lyon_transform_multiply, rt_lyon_transform_rotate, rt_lyon_transform_scale,
rt_lyon_transform_translate, rt_lyon_vertex_buffer_free, rt_lyon_vertex_buffer_get_normal,
rt_lyon_vertex_buffer_get_position, rt_lyon_vertex_buffer_size, rt_lyon_vertex_buffer_to_array,
rt_mem_read_i64, rt_mem_read_u8, rt_mem_write_i64, rt_mem_write_u8, rt_metal_begin_command,
rt_metal_cleanup, rt_metal_cleanup_device, rt_metal_commit_command, rt_metal_create_library,
rt_metal_create_queue, rt_metal_submit, rt_metal_wait_completion, rt_oneapi_device_memory,
rt_oneapi_device_name, rt_oneapi_device_type, rt_oneapi_get_device, rt_oneapi_get_last_error,
rt_oneapi_malloc_shared, rt_oneapi_memcpy_d2h, rt_oneapi_memcpy_h2d, rt_oneapi_set_device,
rt_oneapi_synchronize, rt_opengl_get_last_error, rt_password_hash, rt_password_hash_bcrypt,
rt_password_verify, rt_password_verify_bcrypt, rt_path_normalize, rt_print_err,
rt_process_get_rss_kb, rt_process_output, rt_process_run_capture, rt_ptrace_attach,
rt_ptrace_continue, rt_ptrace_detach, rt_ptrace_get_registers, rt_ptrace_read_memory,
rt_ptrace_single_step, rt_ptrace_wait_stop, rt_ptrace_write_memory, rt_quic_accept,
rt_quic_config_new, rt_quic_config_set_initial_max_streams_bidi,
rt_quic_config_set_max_idle_timeout, rt_quic_conn_close, rt_quic_connect, rt_quic_is_closed,
rt_quic_is_established, rt_quic_on_timeout, rt_quic_recv, rt_quic_send, rt_quic_stream_recv,
rt_quic_stream_send, rt_quic_timeout_as_millis, rt_random_bytes, rt_regex_captures,
rt_regex_captures_len, rt_regex_destroy, rt_regex_find, rt_regex_find_all, rt_regex_find_quick,
rt_regex_is_match, rt_regex_is_match_quick, rt_regex_new, rt_regex_replace,
rt_regex_replace_all, rt_regex_replace_all_quick, rt_regex_replace_quick, rt_regex_split,
rt_regex_split_quick, rt_rocm3d_available, rt_rocm3d_init, rt_rocm3d_shutdown, rt_sdn_parse,
rt_serial_available, rt_serial_set_baud, rt_serial_set_databits, rt_serial_set_parity,
rt_serial_set_stopbits, rt_sftp_download, rt_sftp_init, rt_sftp_mkdir, rt_sftp_readdir,
rt_sftp_rename, rt_sftp_rmdir, rt_sftp_shutdown, rt_sftp_stat, rt_sftp_unlink, rt_sftp_upload,
rt_shell, rt_shell_exec, rt_shell_exit_code, rt_simd_mat4_mul_avx2, rt_simd_mat4_mul_neon,
rt_simd_mat4_mul_sse42, rt_simd_transform_verts_avx2, rt_simd_transform_verts_neon,
rt_simd_transform_verts_sse42, rt_sleep_nanos, rt_ssh_auth_agent, rt_ssh_auth_password,
rt_ssh_auth_pubkey, rt_ssh_channel_close, rt_ssh_channel_read, rt_ssh_channel_write,
rt_ssh_connect, rt_ssh_disconnect, rt_ssh_exec, rt_ssh_get_banner, rt_ssh_is_authenticated,
rt_ssh_set_timeout, rt_ssh_shell, rt_stdin_read, rt_stdin_read_all, rt_stdin_read_bytes,
rt_system, rt_tar_add_data, rt_tar_add_file, rt_tar_close, rt_tar_create, rt_tar_extract,
rt_tar_extract_file, rt_tar_list, rt_tar_open, rt_target_arch_name, rt_target_pointer_bits,
rt_targz_create, rt_targz_extract, rt_tcp_connect, rt_tcp_connect_timeout, rt_term_poll,
rt_term_read_timeout, rt_test_it, rt_time_day, rt_time_hour, rt_time_millis, rt_time_minute,
rt_time_month, rt_time_now_iso, rt_time_now_unix_millis, rt_time_second, rt_time_year,
rt_timestamp_diff_seconds, rt_timestamp_from_iso, rt_timestamp_parse, rt_timestamp_to_iso,
rt_timestamp_to_string, rt_torch_autograd_detach, rt_torch_autograd_requires_grad,
rt_torch_nn_batch_norm, rt_torch_nn_conv2d, rt_torch_nn_cross_entropy, rt_torch_nn_dropout,
rt_torch_nn_linear, rt_torch_nn_max_pool2d, rt_torch_nn_mse_loss, rt_torch_stream_create,
rt_torch_tensor_empty, rt_torch_tensor_eye, rt_torch_tensor_full, rt_torch_tensor_ones,
rt_torch_tensor_rand, rt_torch_tensor_randn, rt_torch_tensor_zeros, rt_torch_torchstream_free,
rt_torch_torchstream_query, rt_torch_torchstream_sync, rt_torch_torchtensor_abs,
rt_torch_torchtensor_acos, rt_torch_torchtensor_arange, rt_torch_torchtensor_argmax,
rt_torch_torchtensor_argmin, rt_torch_torchtensor_asin, rt_torch_torchtensor_atan2,
rt_torch_torchtensor_binary_op, rt_torch_torchtensor_cat_2, rt_torch_torchtensor_cat_3,
rt_torch_torchtensor_cat_4, rt_torch_torchtensor_clone, rt_torch_torchtensor_contiguous,
rt_torch_torchtensor_cos, rt_torch_torchtensor_cpu, rt_torch_torchtensor_det,
rt_torch_torchtensor_div, rt_torch_torchtensor_div_scalar, rt_torch_torchtensor_dot,
rt_torch_torchtensor_exp, rt_torch_torchtensor_eye, rt_torch_torchtensor_flatten,
rt_torch_torchtensor_gather, rt_torch_torchtensor_gelu, rt_torch_torchtensor_inverse,
rt_torch_torchtensor_leaky_relu, rt_torch_torchtensor_linalg_solve,
rt_torch_torchtensor_linspace, rt_torch_torchtensor_log, rt_torch_torchtensor_log_softmax,
rt_torch_torchtensor_matmul, rt_torch_torchtensor_max, rt_torch_torchtensor_max_dim,
rt_torch_torchtensor_mean, rt_torch_torchtensor_mean_dim, rt_torch_torchtensor_min,
rt_torch_torchtensor_min_dim, rt_torch_torchtensor_neg, rt_torch_torchtensor_norm,
rt_torch_torchtensor_permute, rt_torch_torchtensor_permute_2d, rt_torch_torchtensor_permute_3d,
rt_torch_torchtensor_permute_4d, rt_torch_torchtensor_pow, rt_torch_torchtensor_relu,
rt_torch_torchtensor_reshape, rt_torch_torchtensor_reshape_1d, rt_torch_torchtensor_reshape_2d,
rt_torch_torchtensor_reshape_3d, rt_torch_torchtensor_reshape_4d, rt_torch_torchtensor_sigmoid,
rt_torch_torchtensor_sin, rt_torch_torchtensor_slice, rt_torch_torchtensor_softmax,
rt_torch_torchtensor_sqrt, rt_torch_torchtensor_squeeze_dim, rt_torch_torchtensor_stack_2,
rt_torch_torchtensor_stack_3, rt_torch_torchtensor_stack_4, rt_torch_torchtensor_std,
rt_torch_torchtensor_sub_scalar, rt_torch_torchtensor_sum_dim, rt_torch_torchtensor_tan,
rt_torch_torchtensor_tanh, rt_torch_torchtensor_to_float, rt_torch_torchtensor_transpose,
rt_torch_torchtensor_unsqueeze, rt_torch_torchtensor_var, rt_torch_torchtensor_view,
rt_torch_version, rt_uart_read_byte, rt_uart_write_byte, rt_udp_send, rt_uuid_v4, rt_value_add,
rt_value_array_new, rt_value_as_string, rt_value_clone, rt_value_dict_new, rt_value_div,
rt_value_free, rt_value_is_array, rt_value_is_dict, rt_value_is_string, rt_value_lt,
rt_value_mul, rt_value_string, rt_value_sub, rt_value_type, rt_vk3d_available, rt_vk3d_init,
rt_vk3d_shutdown, rt_vk_alloc_cmd_buffer, rt_vk_begin_cmd, rt_vk_cleanup, rt_vk_clear,
rt_vk_create_allocator, rt_vk_create_cmd_pool, rt_vk_create_descriptor_pool,
rt_vk_create_device, rt_vk_create_instance, rt_vk_create_pipeline_cache, rt_vk_destroy_cmd_pool,
rt_vk_destroy_device, rt_vk_destroy_instance, rt_vk_device_name, rt_vk_draw_rect, rt_vk_end_cmd,
rt_vk_get_queue, rt_vk_has_glslc, rt_vk_has_spirv_support, rt_vk_load_spirv, rt_vk_present,
rt_vk_queue_submit, rt_vk_queue_wait_idle, rt_vk_readback, rt_vk_submit, rt_vulkan_api_version,
rt_watchdog_start, rt_watchdog_stop, rt_webgpu_adapter_backend, rt_webgpu_adapter_count,
rt_webgpu_adapter_is_cpu, rt_webgpu_adapter_name, rt_webgpu_cleanup, rt_webgpu_create_device,
rt_webgpu_is_stub, rt_webgpu_submit, rt_wgpu_adapter_backend, rt_wgpu_adapter_name,
rt_wgpu_cleanup, rt_wgpu_create_device, rt_wgpu_create_instance, rt_wgpu_create_shader,
rt_wgpu_get_queue, rt_wgpu_is_stub, rt_wgpu_present, rt_wgpu_request_adapter, rt_wgpu_submit,
rt_write_stdout, rt_ws_close, rt_ws_connect, rt_ws_receive, rt_ws_send, rt_zip_add_data,
rt_zip_add_file, rt_zip_close, rt_zip_create, rt_zip_extract, rt_zip_extract_file, rt_zip_list,
rt_zip_open
```

## Appendix D — bucket (d), dead/orphaned, 185 names

```
rt_aes_gcm_decrypt_hex, rt_aes_gcm_encrypt_hex, rt_audio_sdl2_queued_bytes,
rt_audio_sdl2_submitted_frames, rt_audio_sdl2_underrun_count, rt_bigint_mod_exp,
rt_cuda3d_apply_bloom, rt_cuda3d_apply_fog, rt_cuda3d_clear_depth, rt_cuda3d_clear_framebuffer,
rt_cuda3d_rasterize_triangles, rt_cuda3d_texture_sample, rt_cuda3d_transform_vertices,
rt_ed25519_generate_keypair, rt_gc_allocate, rt_gc_average_collection_time,
rt_gc_collection_count, rt_gc_deallocate, rt_gc_destroy, rt_gc_dump_heap_stats,
rt_gc_dump_object_graph, rt_gc_enable_leak_detection, rt_gc_enable_logging,
rt_gc_enable_verbose, rt_gc_find_objects_by_type, rt_gc_force_collect,
rt_gc_get_collection_frequency, rt_gc_get_fail_on_exceeded, rt_gc_get_max_heap_growth,
rt_gc_get_min_heap_size, rt_gc_get_shared_roots, rt_gc_get_threshold, rt_gc_get_unique_roots,
rt_gc_get_worker_threads, rt_gc_heap_bytes, rt_gc_is_concurrent, rt_gc_is_enabled,
rt_gc_is_limited, rt_gc_is_valid_object, rt_gc_last_collection_time,
rt_gc_leak_detection_enabled, rt_gc_leak_detection_window, rt_gc_live_object_count,
rt_gc_memory_limit, rt_gc_memory_usage_percent, rt_gc_new, rt_gc_object_size, rt_gc_object_type,
rt_gc_register_shared_root, rt_gc_register_unique_root, rt_gc_run_finalizers,
rt_gc_set_collection_frequency, rt_gc_set_concurrent, rt_gc_set_enabled,
rt_gc_set_fail_on_exceeded, rt_gc_set_leak_detection_window, rt_gc_set_logger,
rt_gc_set_max_heap_growth, rt_gc_set_min_heap_size, rt_gc_set_threshold,
rt_gc_set_worker_threads, rt_gc_shared_root_count, rt_gc_total_allocated, rt_gc_total_freed,
rt_gc_tracked_memory, rt_gc_try_allocate, rt_gc_unique_root_count, rt_gc_unlimited,
rt_gc_unregister_shared_root, rt_gc_unregister_unique_root, rt_gc_verbose_stdout,
rt_gc_with_limit, rt_gc_with_limit_gb, rt_gc_with_limit_mb, rt_gc_with_options,
rt_http_parse_json, rt_http_request_body, rt_http_request_header, rt_http_request_method,
rt_http_request_path, rt_http_request_query, rt_http_response_create, rt_http_response_json,
rt_http_response_set_header, rt_http_stringify_json, rt_intel3d_clear_framebuffer,
rt_intel3d_device_count, rt_intel3d_transform_vertices, rt_intel_command_list_close,
rt_intel_command_list_destroy, rt_intel_command_queue_execute, rt_intel_device_get,
rt_intel_fence_create, rt_intel_fence_destroy, rt_intel_fence_wait, rt_intel_kernel_destroy,
rt_intel_kernel_set_arg, rt_intel_module_create, rt_intel_module_destroy, rt_malloc, rt_memcmp,
rt_oneapi_memcpy, rt_process_memory_usage, rt_read_f64, rt_read_i32, rt_read_i64, rt_read_u8,
rt_rocm3d_clear_framebuffer, rt_rocm3d_device_count, rt_rocm3d_rasterize_triangles,
rt_rocm3d_transform_vertices, rt_rt_file_read_text, rt_sdl_clear_quit,
rt_sdl_event_mouse_button, rt_sdl_set_window_title, rt_sdl_window_should_close,
rt_simd_vec4_dot_avx2, rt_simd_vec4_dot_sse42, rt_ssh_add_known_host, rt_ssh_check_host_key,
rt_ssh_forward_close, rt_ssh_forward_local, rt_ssh_forward_remote, rt_ssh_get_host_key,
rt_ssh_get_methods, rt_system_available_memory, rt_system_total_memory, rt_test262_case_count,
rt_test262_case_negative, rt_test262_case_source, rt_test262_corpus_free, rt_test262_eval,
rt_test262_load_corpus, rt_test_skip, rt_time_now_millis, rt_time_now_seconds_f64,
rt_torch_cuda_empty_cache, rt_torch_cuda_max_memory_allocated, rt_torch_cuda_memory_allocated,
rt_torch_nn_avg_pool2d, rt_torch_nn_binary_cross_entropy, rt_torch_nn_embedding,
rt_torch_nn_layer_norm, rt_torch_nn_nll_loss, rt_torch_safetensors_close,
rt_torch_safetensors_get_tensor, rt_torch_safetensors_list_names,
rt_torch_safetensors_num_tensors, rt_torch_safetensors_open, rt_torch_tensor_arange,
rt_torch_tensor_arange_int, rt_torch_tensor_from_i64_data, rt_torch_tensor_full_int_1d,
rt_torch_tensor_full_int_2d, rt_torch_tensor_linspace, rt_torch_tensor_load,
rt_torch_tensor_ones_int_1d, rt_torch_tensor_ones_int_2d, rt_torch_tensor_save,
rt_torch_tensor_zeros_int_1d, rt_torch_tensor_zeros_int_2d, rt_torch_torchtensor_cat,
rt_torch_torchtensor_chunk, rt_torch_torchtensor_eig, rt_torch_torchtensor_index_select,
rt_torch_torchtensor_squeeze, rt_torch_torchtensor_stack, rt_torch_torchtensor_svd,
rt_torch_torchtensor_t, rt_torch_torchtensor_to_float32, rt_torch_torchtensor_to_int,
rt_torch_torchtensor_to_stream, rt_uart_bytes_available, rt_vk3d_begin_frame, rt_vk3d_cmd_draw,
rt_vk3d_create_device, rt_vk3d_create_pipeline, rt_vk3d_create_render_pass,
rt_vk3d_create_swapchain, rt_vk3d_destroy_device, rt_vk3d_end_frame, rt_write_f64, rt_write_i32,
rt_write_i64, rt_write_u8
```

## 8. What this method cannot see

- A name could be dynamically resolvable through `dynamic_sffi::try_call_dynamic`'s generic
  fallback even when absent from SO_EXPORTS, if the interpreter process itself (not just
  `libsimple_runtime.so`) exports the symbol (e.g. statically linked into the seed binary
  itself rather than the shared object) — not checked here; SO_EXPORTS only covers one .so.
- Call-site counts are a per-repo grep over `.spl` text, not a reachability proof — a name with
  "0 real calls" could still be reached via a dynamically-constructed call in a metaprogramming
  path (none were found in a spot check, but the method cannot rule it out in general).
- Bucket (a)/(b) native-definition detection is line-anchored C function-definition syntax; a
  macro-generated definition (X-macro pattern) would not be found and such a name would be
  misclassified into bucket (c). None were found in the 33-name hand-verified sample, but the
  576-name bucket (c) was not individually checked for this.
- The `.so` sampled (`bootstrap-adhoc-20260805-user`) is one specific build variant; a build
  with different feature flags (e.g. GUI backends enabled) could export more symbols and shrink
  the unreachable set — checked two alternates in §2, both showed the same gap for the
  GUI/graphics families specifically, but not exhaustively for every family.
