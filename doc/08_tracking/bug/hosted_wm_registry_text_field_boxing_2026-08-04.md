# Hosted WM startup dies in browser-renderer teardown: text field read back as i64 (seed boxing)

- **ID:** hosted_wm_registry_text_field_boxing_2026-08-04
- **Status:** OPEN
- **Severity:** high (blocks the native hosted WM browser-renderer lane on the rust-seed interpreter)
- **Found by:** Kimi GUI-check lane, 2026-08-04

## Evidence

Launch the hosted WM (`scripts/gui/macos-gui-run.shs` with a GUI-enabled
driver). After window creation, theme install, and backend creation, startup
dies when the browser renderer start/render path unwinds into
`HostedBrowserRendererRegistry._teardown`:

```
error: semantic: method `ends_with` not found on type `i64` (receiver value: 3817473249313)
```

The receiver `3817473249313` (`0x378D3231021`) is the value read back from
`entry.failure_reason` — a `text` field of `HostedBrowserRendererEntry`
(`src/os/hosted/hosted_browser_renderer_registry.spl:317-324`). The struct
instance came from `self.entries[index]` (`[HostedBrowserRendererEntry]`).

## Why it is interesting

The text field decodes as an i64 only after the entry crossed the
array-store/load boundary in the rust-seed interpreter — the documented
"boxing landmine" family (struct/aggregate values mangled across call/array
ABI). Same family as the native-lane "field access on nil receiver" notes in
`theme_package.spl:110-113` and the titlebar title-text bug
(`wm_window_title_text_not_rendered_2026-07-20.md`).

## Repro

```bash
SIMPLE_GUI_ALLOW_RUST_DRIVER=1 sh scripts/gui/macos-gui-run.shs
```

Wait for `[hosted-wm] raster-backend=simple-2d-winit-buffer`; the process dies
before `[hosted-wm] windows-ready` when the browser lane is enabled.
`SIMPLE_HOSTED_WM_NO_BROWSER=1` (added in the same change set) skips the
browser renderer block and avoids this path entirely.

## Fix direction

Not a WM-logic bug: `failure_reason` is always written from `text` values
(`_fail`, `_teardown`). The wrong value appears only when read back from the
entry array under the rust-seed interpreter. Verify how the seed
encodes/decodes struct-valued array elements for `HostedBrowserRendererEntry`
(specifically the `text` fields following several `i64` fields) and align with
the self-hosted runtime behavior. A gated probe printing the entry's field
tags right after `self.entries[index]` names the decode site in one run.
