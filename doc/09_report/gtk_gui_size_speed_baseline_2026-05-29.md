# GTK GUI Size And Speed Baseline

Date: 2026-05-29

## Summary

| Runtime | Status | Binary bytes | Iterations | Total us | Notes |
|---|---|---:|---:|---:|---|
| Simple web renderer | ok | 39056 | 4 | 8274 | render loop via Simple software renderer |
| Simple static cache | ok | n/a | 4 | 71 | retained HTML artifact hot path after persistent warmup |
| Simple persistent SWBC command plan | ok | n/a | 4 | 302582 | disk-backed compact static-shell plan to retained commands |
| Simple hot SWBC command plan cache | ok | n/a | 4 | 85 | in-memory encoded SWBC sidecar cache after persistent warmup |
| Simple retained command hot cache | ok | n/a | 4 | 83 | in-memory retained command list after persistent warmup |
| Simple BrowserBackend cached frame | ok | n/a | 4 | 258 | integrated browser backend unchanged-static-frame cache |
| Simple BrowserBackend no-op frame | ok | n/a | 4 | 59 | explicit event-loop no-change static frame reuse |
| Simple BrowserBackend present cache | ok | n/a | 4 | 82 | cached host-present pixel buffer when framebuffer is unchanged |
| Simple Engine2D retained static pixels | ok | n/a | 4 | 100 | flyweight pixel buffer for unchanged static Engine2D page |
| Simple SWBC prepared reuse | ok | n/a | 4 | 92 | decoded compact static-shell plan reuse loop |
| Simple SWBC command plan | ok | n/a | 4 | 56 | decoded command-only static-shell plan, no HTML artifact |
| GTK | ok | 14472 | 200 | 27532 | widget construction loop; uses xvfb-run when available |

## Comparison Ratios

| Metric | Value |
|---|---:|
| Simple cached BrowserBackend frame per iteration | 64.50 us |
| Simple Engine2D retained static pixels per iteration | 25.00 us |
| GTK widget loop per iteration | 137.66 us |
| GTK per-iteration cost / Simple cached-frame cost | 2.13x |
| GTK per-iteration cost / Simple retained-pixel cost | 5.51x |
| GTK linked closure / Simple linked closure | 13.55x |
| Simple native executable / GTK minimal executable | 2.70x |

## Interpretation

- GTK's minimal executable can be smaller than the generated Simple executable, but its linked shared-library closure is the relevant deployed-size comparison for a standalone GUI runtime.
- The cached Simple BrowserBackend frame path measures unchanged-frame work after the static UI revision key hits; it avoids HTML generation, DOM conversion, layout, raster, and host-present pixel conversion.
- The Simple Engine2D retained static pixels row measures a pure Simple flyweight buffer for unchanged static pages; changed dynamic panes should render into separate regions.
- The Simple benchmark runs with a narrowed SIMPLE_LIB scope of `/home/ormastes/dev/pub/simple/src/lib:/home/ormastes/dev/pub/simple/src/app`, so the interpreter does not need the full repository source tree for this GUI path.
- The GTK speed row measures widget construction on this host under xvfb-run when available, so compare it as a small GUI baseline rather than a full application benchmark.

## Static Shell Size

| Artifact | Bytes |
|---|---:|
| Simple generated full HTML | 248 |
| Simple compact static-shell plan | 171 |
| Simple decoded layout payload estimate | 72 |
| Simple retained command payload | 90 |
| Simple native executable | 39056 |
| Simple executable plus linked shared-library closure | 2401000 |
| GTK minimal executable | 14472 |
| GTK executable plus linked shared-library closure | 32534656 |

## Dependency Scope

| Scope | SPL files |
|---|---:|
| Simple run SIMPLE_LIB | 6859 |
| Full src tree | 10363 |

## Simple Output

- [INFO] JIT compilation failed, falling back to interpreter: HIR lowering error: Unknown type: UITheme
- [gc-warning] Higher-layer module 'std.nogc_sync_mut.sffi.dynamic' (family: nogc_sync_mut) imported in restricted context (family: nogc_async_mut) (higher_layer_runtime_family)
- [gc-warning] Higher-layer module 'std.nogc_sync_mut.io.opengl_sffi' (family: nogc_sync_mut) imported in restricted context (family: nogc_async_mut) (higher_layer_runtime_family)
- [gc-warning] Higher-layer module 'std.nogc_sync_mut.env.types' (family: nogc_sync_mut) imported in restricted context (family: nogc_async_mut) (higher_layer_runtime_family)
- [gc-warning] Higher-layer module 'std.nogc_sync_mut.io.rocm_sffi' (family: nogc_sync_mut) imported in restricted context (family: nogc_async_mut) (higher_layer_runtime_family)
- simple_render_status=ok
- simple_render_iterations=4
- simple_render_total_us=8274
- simple_render_pixels=256000
- simple_cache_schema=simple-web-cache-v1
- simple_render_plan=static_shell_with_dynamic_islands
- simple_dynamic_regions=1
- simple_static_cache_miss_stored=true
- simple_static_cache_hit_iterations=4
- simple_static_cache_memory_hits=4
- simple_static_cache_disk_hits=0
- simple_static_cache_total_us=71
- simple_static_cache_html_bytes=992
- simple_static_disk_plan_warm_stored=true
- simple_static_disk_plan_hit_iterations=4
- simple_static_disk_plan_command_count=20
- simple_static_disk_plan_total_us=302582
- simple_static_plan_cache_warm_stored=true
- simple_static_plan_cache_hit_iterations=4
- simple_static_plan_cache_memory_hits=4
- simple_static_plan_cache_command_count=20
- simple_static_plan_cache_total_us=85
- simple_static_command_cache_warm_stored=true
- simple_static_command_cache_hit_iterations=4
- simple_static_command_cache_memory_hits=4
- simple_static_command_cache_command_count=20
- simple_static_command_cache_total_us=83
- simple_browser_cached_frame_iterations=4
- simple_browser_cached_frame_total_us=258
- simple_browser_static_shell_hits=0
- simple_browser_static_shell_stores=1
- simple_browser_static_frame_hits=8
- simple_browser_static_frame_stores=1
- simple_browser_static_frame_fast_hits=4
- simple_browser_static_frame_fast_stores=1
- simple_browser_cached_frame_pixels=3072
- simple_browser_noop_cached_frame_iterations=4
- simple_browser_noop_cached_frame_hits=4
- simple_browser_noop_cached_frame_total_us=59
- simple_browser_present_cache_iterations=4
- simple_browser_present_cache_total_us=82
- simple_browser_present_cache_pixels=12288
- simple_browser_present_cache_hits=4
- simple_browser_present_cache_stores=1
- simple_browser_present_cache_warm_pixels=3072
- simple_engine2d_solid_status=ok
- simple_engine2d_solid_total_us=100
- simple_engine2d_solid_pixels=256000
- simple_engine2d_solid_cache_hits=4
- simple_engine2d_solid_cache_stores=1
- simple_engine2d_solid_cache_warm_pixels=64000
- simple_static_html_bytes=248
- simple_static_binary_plan_bytes=171
- simple_static_binary_commands=5
- simple_static_layout_payload_bytes=72
- simple_static_command_payload_bytes=90
- simple_static_style_rules=1
- simple_static_text_runs=2
- simple_static_swbc_hit_iterations=4
- simple_static_swbc_prepared_hits=4
- simple_static_command_reuse_count=20
- simple_static_command_reuse_hits=4
- simple_static_swbc_total_us=92
- simple_static_command_plan_valid=true
- simple_static_command_plan_count=20
- simple_static_command_plan_hits=4
- simple_static_command_plan_total_us=56

## GTK Output

- gtk_render_status=ok
- gtk_render_iterations=200
- gtk_widget_total_us=27532

## Simple Linked Dependencies

- /lib64/ld-linux-x86-64.so.2
- /lib/x86_64-linux-gnu/libc.so.6

## GTK Linked Dependencies

- /lib64/ld-linux-x86-64.so.2
- /lib/x86_64-linux-gnu/libatk-1.0.so.0
- /lib/x86_64-linux-gnu/libatk-bridge-2.0.so.0
- /lib/x86_64-linux-gnu/libatspi.so.0
- /lib/x86_64-linux-gnu/libblkid.so.1
- /lib/x86_64-linux-gnu/libbrotlicommon.so.1
- /lib/x86_64-linux-gnu/libbrotlidec.so.1
- /lib/x86_64-linux-gnu/libbsd.so.0
- /lib/x86_64-linux-gnu/libbz2.so.1.0
- /lib/x86_64-linux-gnu/libcairo-gobject.so.2
- /lib/x86_64-linux-gnu/libcairo.so.2
- /lib/x86_64-linux-gnu/libcap.so.2
- /lib/x86_64-linux-gnu/libc.so.6
- /lib/x86_64-linux-gnu/libdatrie.so.1
- /lib/x86_64-linux-gnu/libdbus-1.so.3
- /lib/x86_64-linux-gnu/libepoxy.so.0
- /lib/x86_64-linux-gnu/libexpat.so.1
- /lib/x86_64-linux-gnu/libffi.so.8
- /lib/x86_64-linux-gnu/libfontconfig.so.1
- /lib/x86_64-linux-gnu/libfreetype.so.6
- /lib/x86_64-linux-gnu/libfribidi.so.0
- /lib/x86_64-linux-gnu/libgcrypt.so.20
- /lib/x86_64-linux-gnu/libgdk-3.so.0
- /lib/x86_64-linux-gnu/libgdk_pixbuf-2.0.so.0
- /lib/x86_64-linux-gnu/libgio-2.0.so.0
- /lib/x86_64-linux-gnu/libglib-2.0.so.0
- /lib/x86_64-linux-gnu/libgmodule-2.0.so.0
- /lib/x86_64-linux-gnu/libgobject-2.0.so.0
- /lib/x86_64-linux-gnu/libgpg-error.so.0
- /lib/x86_64-linux-gnu/libgraphite2.so.3
- /lib/x86_64-linux-gnu/libgtk-3.so.0
- /lib/x86_64-linux-gnu/libharfbuzz.so.0
- /lib/x86_64-linux-gnu/libjpeg.so.8
- /lib/x86_64-linux-gnu/liblz4.so.1
- /lib/x86_64-linux-gnu/liblzma.so.5
- /lib/x86_64-linux-gnu/libmd.so.0
- /lib/x86_64-linux-gnu/libmount.so.1
- /lib/x86_64-linux-gnu/libm.so.6
- /lib/x86_64-linux-gnu/libpango-1.0.so.0
- /lib/x86_64-linux-gnu/libpangocairo-1.0.so.0
- /lib/x86_64-linux-gnu/libpangoft2-1.0.so.0
- /lib/x86_64-linux-gnu/libpcre2-8.so.0
- /lib/x86_64-linux-gnu/libpixman-1.so.0
- /lib/x86_64-linux-gnu/libpng16.so.16
- /lib/x86_64-linux-gnu/libselinux.so.1
- /lib/x86_64-linux-gnu/libsystemd.so.0
- /lib/x86_64-linux-gnu/libthai.so.0
- /lib/x86_64-linux-gnu/libwayland-client.so.0
- /lib/x86_64-linux-gnu/libwayland-cursor.so.0
- /lib/x86_64-linux-gnu/libwayland-egl.so.1
- /lib/x86_64-linux-gnu/libX11.so.6
- /lib/x86_64-linux-gnu/libXau.so.6
- /lib/x86_64-linux-gnu/libxcb-render.so.0
- /lib/x86_64-linux-gnu/libxcb-shm.so.0
- /lib/x86_64-linux-gnu/libxcb.so.1
- /lib/x86_64-linux-gnu/libXcomposite.so.1
- /lib/x86_64-linux-gnu/libXcursor.so.1
- /lib/x86_64-linux-gnu/libXdamage.so.1
- /lib/x86_64-linux-gnu/libXdmcp.so.6
- /lib/x86_64-linux-gnu/libXext.so.6
- /lib/x86_64-linux-gnu/libXfixes.so.3
- /lib/x86_64-linux-gnu/libXinerama.so.1
- /lib/x86_64-linux-gnu/libXi.so.6
- /lib/x86_64-linux-gnu/libxkbcommon.so.0
- /lib/x86_64-linux-gnu/libXrandr.so.2
- /lib/x86_64-linux-gnu/libXrender.so.1
- /lib/x86_64-linux-gnu/libz.so.1
- /lib/x86_64-linux-gnu/libzstd.so.1

## Notes

- Set SKIP_SIMPLE_NATIVE=1 to skip Simple native binary size measurement for faster smoke runs.
- GTK executable size is reported separately from the linked shared-library closure.
- GTK speed uses xvfb-run when available; otherwise it is unavailable on headless hosts without a display.
- Override SIMPLE_RUN_LIB or SIMPLE_NATIVE_LIB to audit broader or narrower source roots.
- Simple speed measures the pure software HTML-to-pixel path and records the shared render optimization profile.
