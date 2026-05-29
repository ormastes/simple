# GTK GUI Size And Speed Baseline

Date: 2026-05-29

## Summary

| Runtime | Status | Binary bytes | Iterations | Total us | Notes |
|---|---|---:|---:|---:|---|
| Simple web renderer | ok | n/a | 4 | 5614 | render loop via Simple software renderer |
| Simple static cache | ok | n/a | 4 | 1346 | persistent HTML artifact cache hit loop |
| Simple persistent SWBC command plan | ok | n/a | 4 | 397256 | disk-backed compact static-shell plan to retained commands |
| Simple hot SWBC command plan cache | ok | n/a | 4 | 133880 | in-memory encoded SWBC sidecar cache after persistent warmup |
| Simple SWBC prepared reuse | ok | n/a | 4 | 78 | decoded compact static-shell plan reuse loop |
| Simple SWBC command plan | ok | n/a | 4 | 38 | decoded command-only static-shell plan, no HTML artifact |
| GTK | ok | 14472 | 200 | 24415 | widget construction loop; uses xvfb-run when available |

## Static Shell Size

| Artifact | Bytes |
|---|---:|
| Simple generated full HTML | 248 |
| Simple compact static-shell plan | 171 |
| Simple decoded layout payload estimate | 72 |
| Simple retained command payload | 90 |
| GTK minimal executable | 14472 |
| GTK executable plus linked shared-library closure | 32534656 |

## Simple Output

- [INFO] JIT compilation failed, falling back to interpreter: HIR lowering error: let binding failed: Wildcard - complex patterns are not yet supported in let bindings
- [memory-guard] SIMPLE_LIB=/home/ormastes/dev/pub/simple/src contains 600+ .spl files — consider narrowing scope to avoid memory bloat
- simple_render_status=ok
- simple_render_iterations=4
- simple_render_total_us=5614
- simple_render_pixels=256000
- simple_cache_schema=simple-web-cache-v1
- simple_render_plan=static_shell_with_dynamic_islands
- simple_dynamic_regions=1
- simple_static_cache_miss_stored=true
- simple_static_cache_hit_iterations=4
- simple_static_cache_memory_hits=4
- simple_static_cache_disk_hits=0
- simple_static_cache_total_us=1346
- simple_static_disk_plan_warm_stored=false
- simple_static_disk_plan_hit_iterations=4
- simple_static_disk_plan_command_count=20
- simple_static_disk_plan_total_us=397256
- simple_static_plan_cache_warm_stored=true
- simple_static_plan_cache_hit_iterations=4
- simple_static_plan_cache_memory_hits=4
- simple_static_plan_cache_command_count=20
- simple_static_plan_cache_total_us=133880
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
- simple_static_swbc_total_us=78
- simple_static_command_plan_valid=true
- simple_static_command_plan_count=20
- simple_static_command_plan_hits=4
- simple_static_command_plan_total_us=38

## GTK Output

- gtk_render_status=ok
- gtk_render_iterations=200
- gtk_widget_total_us=24415

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

- Set SKIP_SIMPLE_NATIVE=0 to add Simple native binary bytes; default skips the slow native build.
- GTK executable size is reported separately from the linked shared-library closure.
- GTK speed uses xvfb-run when available; otherwise it is unavailable on headless hosts without a display.
- Simple speed measures the pure software HTML-to-pixel path and records the shared render optimization profile.
