# GTK GUI Size And Speed Baseline

Date: 2026-05-29

## Summary

| Runtime | Status | Binary bytes | Iterations | Total us | Notes |
|---|---|---:|---:|---:|---|
| Simple web renderer | ok | n/a | 4 | 5352 | render loop via Simple software renderer |
| Simple static cache | ok | n/a | 4 | 1319 | persistent HTML artifact cache hit loop |
| Simple SWBC prepared reuse | ok | n/a | 4 | 80 | decoded compact static-shell plan reuse loop |
| GTK | unavailable | 14472 | 200 | n/a | no_display |

## Static Shell Size

| Artifact | Bytes |
|---|---:|
| Simple generated full HTML | 248 |
| Simple compact static-shell plan | 171 |
| Simple decoded layout payload estimate | 72 |
| Simple retained command payload | 90 |
| GTK minimal executable | 14472 |

## Simple Output

- [INFO] JIT compilation failed, falling back to interpreter: HIR lowering error: let binding failed: Wildcard - complex patterns are not yet supported in let bindings
- [memory-guard] SIMPLE_LIB=/home/ormastes/dev/pub/simple/src contains 600+ .spl files — consider narrowing scope to avoid memory bloat
- simple_render_status=ok
- simple_render_iterations=4
- simple_render_total_us=5352
- simple_render_pixels=256000
- simple_cache_schema=simple-web-cache-v1
- simple_render_plan=static_shell_with_dynamic_islands
- simple_dynamic_regions=1
- simple_static_cache_miss_stored=true
- simple_static_cache_hit_iterations=4
- simple_static_cache_memory_hits=4
- simple_static_cache_disk_hits=0
- simple_static_cache_total_us=1319
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
- simple_static_swbc_total_us=80

## GTK Output

- gtk_render_status=unavailable
- gtk_reason=no_display

## Notes

- Set SKIP_SIMPLE_NATIVE=0 to add Simple native binary bytes; default skips the slow native build.
- GTK size is the minimal linked executable size, not the full shared-library closure unless inspected with ldd.
- GTK speed is unavailable on headless hosts without a display.
- Simple speed measures the pure software HTML-to-pixel path and records the shared render optimization profile.
