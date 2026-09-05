# WM Glass Theme on Host and SimpleOS — Domain Research

## Reference Material

The repository records the original Stitch project as
`14134637940805933672`. Its checked-in snapshot specifies a dark tonal palette,
12px rounded geometry, translucent/frosted surfaces, blur, distinct active and
inactive shadows, and system-style typography. These are semantic material
properties, not merely a dark color palette.

The current `aetheric_dark` package cites the Stitch raw reference and contains
RGBA surfaces, translucent borders, elevation shadows, and glass accents. It is
therefore the closest existing package authority, though its projection into
WM/Web renderers is incomplete.

## Glass Material Contract

A faithful macOS-like glass material needs all of the following to survive the
pipeline:

1. backdrop-derived fill or a declared solid accessibility fallback;
2. surface alpha and blur/saturation;
3. border color, alpha, width, and corner radius;
4. layered active/inactive shadows;
5. readable foreground and secondary text tokens;
6. focus/active state and reduced-transparency policy.

Color-only token adapters cannot represent this contract. The owning theme
model needs typed material semantics which renderers lower according to their
capabilities, while evidence records any fallback.

## Product Choice Exposed by History

The repository currently contains three plausible identities: the packaged
`aetheric_dark` theme, the original dark Stitch Glass snapshot, and the newer
light Aqua/Mac-like WM defaults. Selecting among them changes visible product
behavior, migration scope, and baseline pixels; it cannot be inferred safely
from implementation convenience.
