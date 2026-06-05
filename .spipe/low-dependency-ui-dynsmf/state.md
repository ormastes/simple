# Feature: low-dependency-ui-dynsmf

## Raw Request
$sp_dev
refactor ui dependency and add smf dynlib feature.  research web about similar situations. and research local. and detail plans for multiple agents in pherallel.
Tui dependency minimize and no dependency to gui but ui.
Gui, web renderer, minimize dependency, let only gui widget depend html renderer component and css only used components to loaded. Refactor to highly low dependency arch.
lets make common libs, which are std lib like, file io, net io, 2d renderer, web renderer, gui renderer, tui renderer, be precompiled dynsmf. unless specify to not to load all or specific lib by arg or env. Load them as smf dynlib. however there should be way to unload from session to test lib itself in test in interpreter mode.

## Task Type
feature

## Refined Goal
Refactor the Simple UI and renderer stack into low-dependency UI contracts and loadable precompiled SMF dynlibs for standard library-like capabilities, with explicit opt-in/opt-out controls and interpreter-testable unload support.

## Acceptance Criteria
- AC-1: Local and web research artifacts identify the current dependency hot spots, prior repo work, and comparable dynamic loading/lazy component patterns.
- AC-2: Requirement options and NFR options exist with pros, cons, and effort estimates, and final requirements are not written until the user selects options.
- AC-3: TUI imports depend only on common UI contracts and TUI renderer code; they do not import GUI, HTML renderer, browser, or CSS implementation modules.
- AC-4: GUI, web, Tauri, Electron, VSCode, browser, and TUI-web adapters consume shared UI/web-render contracts while implementation modules remain behind adapter or widget boundaries.
- AC-5: HTML renderer and CSS implementation modules are loaded only for components or adapters that need them; non-web/non-HTML lanes can prove they do not pull the HTML/CSS closure.
- AC-6: File IO, net IO, 2D renderer, web renderer, GUI renderer, and TUI renderer libraries have precompiled dynSMF manifest entries and load through the SMF dynlib path by default.
- AC-7: CLI arguments and environment variables can disable all auto dynSMF loading or disable specific dynSMF libraries.
- AC-8: A session-scoped dynSMF handle can unload a library and then reload it in interpreter-mode tests so the library can test itself without stale session state.
- AC-9: System and unit SPipe specs cover dependency boundaries, dynSMF default loading, opt-out controls, and unload/reload behavior without placeholder assertions.
- AC-10: Parallel agent plan assigns independent work lanes with inputs, outputs, sequencing, conflict boundaries, and verification gates.

## Scope Exclusions
- No automatic final requirement selection.
- No release or push until verify produces `STATUS: PASS`.
- No edits to unrelated dirty thread-enhancement or compiler Rust work unless required by selected requirements.

## Phase
requirements-selection-pending

## Log
- dev: Created combined SPipe lane with 10 acceptance criteria for UI dependency minimization and SMF dynlib loading.
- research: Added local and domain research plus TLDR companions.
- requirements: Added feature and NFR option sets; final requirements are intentionally pending user selection.
- plan: Added parallel multi-agent task plan with conflict boundaries and sequencing.
- research: Added corrected exact-prefix import closure evidence. Base `app.ui.tui` currently has zero web/TUI-web/HTML/browser/CSS/GUI implementation modules in closure; common `app.ui.render.widgets -> app.ui.render.html_widgets` is the first split target.
