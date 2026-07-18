# GTK GUI Size And Speed Baseline

Date: 2026-05-30

## Summary

| Runtime | Status | Binary bytes | Iterations | Total us | Notes |
|---|---|---:|---:|---:|---|
| Simple web renderer | ok | n/a | 4 | 1 | retained framebuffer for unchanged Simple web HTML |
| Simple open/startup | ok | n/a | 1 | 213 | first retained cache creation plus first framebuffer warm render |
| Simple minimal retained renderer | unavailable | n/a | 4 | n/a | minimized dependency entry using only retained Simple web framebuffer |
| Simple static cache | ok | n/a | 4 | n/a | retained HTML artifact hot path after persistent warmup |
| Simple persistent SWBC command plan | ok | n/a | 4 | n/a | disk-backed compact static-shell plan to retained commands |
| Simple hot SWBC command plan cache | ok | n/a | 4 | n/a | in-memory encoded SWBC sidecar cache after persistent warmup |
| Simple retained command hot cache | ok | n/a | 4 | n/a | in-memory retained command list after persistent warmup |
| Simple BrowserBackend cached frame | ok | n/a | 4 | 1 | integrated browser backend unchanged-static-frame cache |
| Simple BrowserBackend no-op frame | ok | n/a | 4 | n/a | explicit event-loop no-change static frame reuse |
| Simple BrowserBackend present cache | ok | n/a | 4 | n/a | cached host-present pixel buffer when framebuffer is unchanged |
| Simple Engine2D retained static pixels | ok | n/a | 4 | n/a | flyweight pixel buffer for unchanged static Engine2D page |
| Simple SWBC prepared reuse | ok | n/a | 4 | n/a | decoded compact static-shell plan reuse loop |
| Simple vector text render | ok | n/a | 4 | 69 | Engine2D glyph rendering into retained text pixels |
| Simple SWBC command plan | ok | n/a | 4 | 69 | decoded command-only static-shell plan or retained-mode text workload |
| GTK | ok | 14472 | 20 | 526 | widget construction loop; uses xvfb-run when available |
| GTK open/startup | ok | n/a | 1 | 68639 | gtk_init_check plus first window/label construction |

## Comparison Ratios

| Metric | Value |
|---|---:|
| Simple open/startup | 213 us |
| GTK open/startup | 68639 us |
| Simple cached BrowserBackend frame per iteration | 0.25 us |
| Simple Engine2D retained static pixels per iteration | n/a us |
| Simple minimal retained renderer per iteration | n/a us |
| Simple static text command-plan per iteration | 17.25 us |
| Simple vector text render per iteration | 17.25 us |
| GTK widget loop per iteration | 26.30 us |
| GTK per-iteration cost / Simple cached-frame cost | 105.20x |
| GTK per-iteration cost / Simple retained-pixel cost | n/ax |
| GTK linked closure / Simple linked closure | n/ax |
| GTK linked closure / Simple minimal retained closure | n/ax |
| Simple native executable / GTK minimal executable | n/ax |
| Simple minimal retained executable / GTK minimal executable | n/ax |

## Interpretation

- GTK's minimal executable can be smaller than the generated Simple executable, but its linked shared-library closure is the relevant deployed-size comparison for a standalone GUI runtime.
- The cached Simple BrowserBackend frame path measures unchanged-frame work after the static UI revision key hits; it avoids HTML generation, DOM conversion, layout, raster, and host-present pixel conversion.
- The Simple minimal retained renderer row builds a separate dependency-minimized entry that imports only the retained Simple web framebuffer path.
- The Simple Engine2D retained static pixels row measures a pure Simple flyweight buffer for unchanged static pages; changed dynamic panes should render into separate regions.
- The Simple benchmark runs with a narrowed SIMPLE_LIB scope of `/home/ormastes/dev/pub/simple/src/lib:/home/ormastes/dev/pub/simple/src/app`, so the interpreter does not need the full repository source tree for this GUI path.
- The GTK speed row measures widget construction on this host under xvfb-run when available, so compare it as a small GUI baseline rather than a full application benchmark.

## GTK Evidence Gate

| Field | Value |
|---|---:|
| scene_id | wm-static-text-grid |
| status | pass |
| reason | pass |
| sample_status | ok |
| trial_status | ok |
| min_iterations | 3 |
| min_trials | 3 |
| simple_frame_us | 1 |
| gtk_frame_us | 26 |
| simple_open_us | 213 |
| gtk_open_us | 68639 |
| simple_text_us | 17 |
| gtk_text_us | 26 |
| simple_vector_text_total_us | 69 |
| simple_vector_text_pixels | 1676 |
| simple_vector_text_ink_pixels | 5268 |
| simple_vector_text_warm_ink_pixels | 1317 |
| simple_vector_text_checksum | 212444 |
| simple_vector_text_deterministic | true |
| simple_iterations | 4 |
| gtk_iterations | 20 |
| simple_trial_count | 3 |
| simple_failed_trial_count | 0 |
| simple_timeout_trial_count | 0 |
| gtk_trial_count | 3 |
| gtk_failed_trial_count | 0 |

## Static Shell Size

| Artifact | Bytes |
|---|---:|
| Simple generated full HTML | 201 |
| Simple compact static-shell plan | 1 |
| Simple decoded layout payload estimate | 1 |
| Simple retained command payload | 56 |
| Simple native executable | n/a |
| Simple minimal retained renderer executable | n/a |
| Simple executable plus linked shared-library closure | n/a |
| Simple minimal retained executable plus linked shared-library closure | n/a |
| GTK minimal executable | 14472 |
| GTK executable plus linked shared-library closure | 32534656 |

## Dependency Scope

| Scope | SPL files |
|---|---:|
| Simple run SIMPLE_LIB | 6997 |
| Full src tree | 10517 |

## Simple Output

- simple_render_status=ok
- simple_open_total_us=205
- simple_render_iterations=4
- simple_render_total_us=1
- simple_render_pixels=256000
- simple_render_cache_hits=4
- simple_render_cache_stores=1
- simple_browser_cached_frame_total_us=1
- simple_static_command_plan_total_us=64
- simple_static_command_plan_count=5268
- simple_vector_text_total_us=64
- simple_vector_text_pixels=1676
- simple_vector_text_ink_pixels=5268
- simple_vector_text_warm_ink_pixels=1317
- simple_vector_text_checksum=212444
- simple_vector_text_deterministic=true
- simple_static_html_bytes=201
- simple_static_binary_plan_bytes=1
- simple_static_layout_payload_bytes=1
- simple_static_command_payload_bytes=56

## Simple Minimal Output


## GTK Output

- gtk_render_status=ok
- gtk_render_iterations=20
- gtk_open_total_us=71257
- gtk_widget_total_us=526

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
- Simple run timeout is 60s with 10s kill-after; Simple native-build timeout is 240s with 10s kill-after.
- Override SIMPLE_RUN_LIB or SIMPLE_NATIVE_LIB to audit broader or narrower source roots.
- Simple speed measures the pure software HTML-to-pixel path and records the shared render optimization profile.
