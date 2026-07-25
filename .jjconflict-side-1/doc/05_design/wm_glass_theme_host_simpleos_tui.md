<!-- codex-design -->
# TUI Design: WM Glass Theme on Host and SimpleOS

There is no TUI product surface for this feature. The operator-facing textual
surface is structured evidence emitted by host and QEMU checkers.

Each record uses `wm-glass-theme-evidence-v1` and includes theme identity,
manifest/material hashes, canonical route, capabilities/fallbacks, interaction
revisions, framebuffer provenance, performance measurements and artifact paths.
Unknown or missing fields fail closed. Serial output stays compact and does not
embed CSS or pixel buffers.

```text
bootstrap record -> interaction records -> frame/capture records -> verdict
```
