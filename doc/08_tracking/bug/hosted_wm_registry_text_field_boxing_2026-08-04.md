# Hosted WM startup dies in browser-renderer teardown: text field read back as i64 (seed boxing)

- **ID:** hosted_wm_registry_text_field_boxing_2026-08-04
- **Status:** CLOSED 2026-11-11 — FIXED on release; verified by lane ne11 on fresh seed 46fe8f6b6def
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

---

## 2026-11-11 addendum — lane ne11 (P3 traverse, batch ne11)

**Verdict: FIXED on release — the seed array-round-trip boxing defect no longer reproduces.**

The 2026-10-27 triage kept this open as `valid/untested` with "no causal code
fix shown"; this lane executed the failure mechanism on the fresh tracked seed
and it is green.

- **Verification (seed-smoke, tracked `bin/simple.exe` build-commit `46fe8f6b6def`,
  `SIMPLE_LIB=src`, both `--mode` default/JIT and `--mode=interpreter`):**
  - Probe 1 — exact reported shape: struct with `text` field following `i64`
    fields, literal-constructed, stored in an array, read back, text method
    called on the field: prints `failure_reason=browser teardown failed` /
    `ends_with(...)=true`, exit 0.
  - Probe 2 — the registry shape: a `Registry` class holding
    `entries: [HostedBrowserRendererEntry]`, `static fn create`, plain
    method reading `self.entries[index]` then `entry.failure_reason.ends_with(...)`:
    `ends_with=true`, exit 0, both engines. (An earlier probe variant using a
    non-Simple `fn __init` constructor segfaulted on an *uninitialized* array —
    a probe bug, not this defect; corrected to `static fn create`.)
- **Fixing change:** not individually attributable on this no-cargo lane — the
  fix is among the 2026-11 seed aggregate/Option/array decode fixes now built
  into the refreshed seed (`fa6939eb4b9e` unbox tuple destructuring leaves,
  `90f9d6b7c15e` flat Option encoding for array get/at, refresh
  `f919ff81626d`; same family as the earlier aggregate layout fix
  `53dbda67e9eb`). Closure is claimed on executed evidence, not on a cited
  single commit.
- The full hosted-WM launch path (`SIMPLE_GUI_ALLOW_RUST_DRIVER=1 sh
  scripts/gui/macos-gui-run.shs`) is a GUI lane outside this host; the
  documented decode defect itself is proven resolved at the exact ABI boundary
  it was filed against. `SIMPLE_HOSTED_WM_NO_BROWSER=1` remains a valid bypass
  but is no longer required to avoid this defect.
