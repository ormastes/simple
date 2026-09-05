# Web showcase retained document I/O

Source: `test/03_system/ui_showcase/showcase_web_retained_io_spec.spl`.

`ScreenWebHost` caches the last successfully published HTML document. Repeated
unchanged frames still count as successful presentations but perform no file
write. A scene mutation produces different HTML and exactly one additional
write. Failed writes never update the retained cache or counter.

The shared owner loop derives a scene ID from the showcase prefix, starts at
scene generation 1, and advances generation
after every applied input event. Web skips serialization and I/O when the
positive scene-ID/generation pair is unchanged. GUI reuses retained pixels for
that same identity, avoiding repeat rasterization while still presenting cached pixels
to preserve native window pacing. Generation zero remains uncached for direct
callers that do not provide owner identity.

When a newer generation serializes to byte-identical HTML, web commits the new
identity even though no write is needed. Subsequent frames then take the
identity fast path instead of repeatedly paying serialization cost. The spec
asserts both serialization and write counters.

This removes redundant filesystem work from the web showcase warm path while
preserving event polling and frame-count behavior.

A valid browser resize event updates the host dimensions and invalidates the
retained scene identity before the event is returned. The next frame therefore
uses the new viewport and publishes one resized document; stale-sized cached
HTML cannot be accepted.
