# `widget × host-WM` headless capture: `ppm-write-failed` on the DEFAULT path, passes with an explicit path — cause not yet identified

- **ID:** wm_widget_headless_default_ppm_path_write_fails_2026-07-25
- **Status:** OPEN — reproducible, well-characterised, **root cause unknown**
- **Severity:** medium — the cell cannot pass unattended; it passes only when
  `SIMPLE_WM_HEADLESS_CAPTURE_PPM` is set to a path outside the repo.

## Reproduction (3 runs, deterministic by path)

Binary: session-built full CLI. Invocation otherwise identical each time
(`SIMPLE_WM_HEADLESS_CAPTURE=1 SIMPLE_TIMEOUT_SECONDS=900 <cli> run
examples/06_io/ui/wm_widget_showcase_gui.spl`).

| run | `SIMPLE_WM_HEADLESS_CAPTURE_PPM` | result |
|---|---|---|
| 3 | unset (default path) | `status=fail reason=ppm-write-failed` |
| 4 | set to a scratchpad path | **`status=pass reason=ok`** |
| 5 | unset (default path) | `status=fail reason=ppm-write-failed` |

So it is **path-dependent and reproducible**, not intermittent. Run 5 was run
specifically to rule out a transient, after an earlier draft of this
investigation wrongly credited run 4's pass to the override without a control.

Run 4's evidence is genuine, independently verified (not just the status line):
`P6 660 840 255`, 1,663,215 bytes = 554400×3+15 exactly, 40 distinct byte
values, nonzero 548,919/554,400. (Caveat: three byte values each occur exactly
364,233 times — one flat background colour over ~66% of the frame, so this is a
weaker frame than the `widget × headless` PASS's 74 distinct values.)

## Default path resolution — verified correct

`run_headless_capture` (`examples/06_io/ui/wm_widget_showcase_gui.spl:521-573`):

```
val tmp_root = path_join(repo_root, "build/tmp")     # :523
dir_create_all(tmp_root)                             # :524  <-- return IGNORED
...
val ppm_path = env_get("SIMPLE_WM_HEADLESS_CAPTURE_PPM")
               ?? path_join(tmp_root, "wm_widget_showcase_headless_capture.ppm")   # :568
val ppm_bytes = encode_ppm_p6(W.to_u32(), H.to_u32(), present_pixels)              # :569
if not file_write_bytes(ppm_path, ppm_bytes):                                      # :570
```

- `repo_root` logged as `/home/ormastes/dev/pub/simple` in **both** the failing
  and passing runs — identical, so not a resolution difference.
- `path_join` (`:148-151`) is trivially correct (adds `/` unless present).
- Resolved default path is therefore
  `/home/ormastes/dev/pub/simple/build/tmp/wm_widget_showcase_headless_capture.ppm`.

## Ruled out (do not re-test these)

1. **Directory missing / not writable** — `build/tmp` exists, is mode 775, owned
   by the running user; a shell `touch` probe succeeds. 1.4 TB free on that fs.
2. **`file_write_bytes` cannot write there** — a standalone `.spl` probe writing
   via `file_write_bytes` returned `true` for the repo-relative path, the
   repo-absolute path, and a scratchpad path.
3. **Payload size** — a probe writing **1,663,215 bytes** (the exact capture
   size) to the **exact** default filename returned `true` and produced the file.
4. **Name collision** — nothing occupies that path (not a directory, not a stale
   file) before the run.
5. **Transient failure** — run 5 reproduced the failure with the default path
   after run 4 passed.
6. **`path_join` malformation** — read and verified; also note it is a *local*
   function in this example (`:148`), not the stdlib one.

## What is still unexplained

The write fails from inside the showcase but succeeds from a standalone probe to
the same path with the same byte count. Differences not yet eliminated:

- The showcase spawns a child that writes its own frame PPMs into the **same**
  `build/tmp` directory, and `process_kill(child_pid)` runs immediately before
  the parent's write (`:561`). A file-handle / concurrent-writer interaction in
  that directory has not been excluded.
- `encode_ppm_p6`'s output is only exercised on the failing path; the override
  path proves the encoder works, but the two runs are not otherwise byte-compared.
- `dir_create_all`'s ignored return (`:524`) means a directory-layer failure would
  surface *here*, mislabelled as a write failure. Worth checking the return before
  anything else — it is the cheapest remaining probe.

## Recommended next steps

1. Check `dir_create_all(tmp_root)`'s return value at `:524` and emit a distinct
   reason (e.g. `tmp-root-create-failed`) — this reason code currently absorbs at
   least two different failures and is why the diagnosis stalled.
2. Have the failure branch (`:570-573`) print `ppm_path` and `ppm_bytes.len()`.
   It currently reports only `ppm-write-failed`, so the actual path and payload
   size at failure time are invisible — every fact above had to be reconstructed
   externally.
3. Only then look for the concurrent-writer interaction.

## Related

- `doc/08_tracking/bug/examples_isolation_buffers_output_lost_on_timeout_2026-07-25.md`
  — the two *earlier* obstacles on this same lane (output buffering, 10s
  watchdog). All three had to be cleared in order before this one became visible.
