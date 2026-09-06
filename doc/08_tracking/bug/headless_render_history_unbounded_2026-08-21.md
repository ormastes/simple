# Headless render history retained every HTML snapshot

## Status

Fixed on 2026-08-21.

## Problem

`NoneBackend.render` appended each complete rendered HTML document to
`render_history`. A long-lived `HeadlessApp` that processed events through
`run_single_event` therefore retained memory proportional to the number of
events multiplied by the rendered document size. `clear_history` was the only
release mechanism and callers were not required to invoke it.

## Resolution

The backend now maintains a cumulative render counter while retaining the most
recent 64 HTML snapshots in a circular buffer. `render_count` preserves its
observable cumulative-count behavior. `html_at` continues to address renders
by their absolute ordinal and returns an empty string when that render has been
evicted, matching its existing unavailable-index behavior.

The focused regression renders 80 times and verifies a cumulative count of 80,
a retained count of 64, eviction of render 15, and availability of renders 16
and 79.
