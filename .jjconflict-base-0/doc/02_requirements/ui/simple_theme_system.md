# Feature Requirements: Simple Theme System

## REQ-001: Unified CSS/HTML Setup
- The system must support a `.simple-theme` file format that uses standard CSS syntax (`:root { --var: val; }`) to define theme tokens.
- Both the Simple GUI Library and the Simple Window Manager must use this common theme format.

## REQ-002: Token-to-CSS and CSS-to-Token
- Provide utilities to generate CSS from `UITheme` and `GlassDesignTokens`.
- Provide a parser that extracts `UITheme` and `GlassDesignTokens` from a `.simple-theme` CSS file.

## REQ-003: Stitch Round-Trip Integration
- The `theme-sync` tool must be updated to support the `.simple-theme` format.
- `simple theme-sync pull` should be able to update a `.simple-theme` file from a Stitch snapshot.
- `simple theme-sync push` should be able to generate a Stitch payload from a `.simple-theme` file.

## REQ-004: Live Theme Reloading
- The Window Manager must be able to reload its visual style (numeric tokens) when the `.simple-theme` file is updated.
- Web-based UIs must update their CSS custom properties when the theme changes.
