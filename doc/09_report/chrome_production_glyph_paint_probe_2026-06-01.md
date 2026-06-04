# Chrome Production Glyph Paint Probe

- status: fail-closed
- sample: `site_0_google`
- baseline production divergence: `2717` different pixels
- strict bound: `2717` different pixels

## Attempted Routes

| Route | Different pixels | Result |
|-------|------------------|--------|
| Generic layout renderer for famous-site HTML | `6187` | Regressed strict bound |
| Engine2D matched four-line paint | `3846` | Regressed strict bound |
| Engine2D first-line paint | `3045` | Regressed strict bound |
| Engine2D first word (`Google`) | `2834` | Regressed strict bound |
| Engine2D first four letters (`Goog`) | `2780` | Regressed strict bound |
| Engine2D first glyph (`G`) | `2745` | Regressed strict bound |

## Conclusion

The current production layout diagnostic still matches Chrome's four text lines,
but direct bitmap glyph paint does not reduce the strict different-pixel metric.
The next code slice should implement Chrome-like antialias/proportional glyph
paint and compositing before replacing the rectangle-only production corpus path.
The existing bounded production probe was restored and passes at `2717`
different pixels.
