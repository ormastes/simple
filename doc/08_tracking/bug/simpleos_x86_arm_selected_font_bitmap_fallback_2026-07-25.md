# SimpleOS x86/ARM selected-font bitmap fallback

**Status:** Fixed in source; guest runtime evidence pending a refreshed
pure-Simple self-host.

## Symptom

The x86_64 and AArch64 desktop entries continued rendering with bitmap text
when selected font media or registration failed. RV64 already returned before
rendering, so architecture behavior and font evidence were inconsistent.

## Root cause and fix

The two entries owned permissive boot logic, and x86_64 duplicated single-face
registration. Both now reuse
`simpleos_desktop_register_selected_fonts_from_vfs()` and return before
Engine2D creation on mount or registration failure. The retained x86 evidence
row separately validates the exact registry-owned short-alias bytes it names
before reporting the pinned hash; shared registration still prefers the long
path.

## Regression

The production desktop and font-staging specs require mount → shared
registration → Engine2D ordering, both fatal paths, and absence of the former
`font unavailable fallback=bitmap` branch.
