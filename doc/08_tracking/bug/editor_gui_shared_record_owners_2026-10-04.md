# GUI shell and SDL bridge record ownership

The completed 9d484 early Phase 4 run reported unresolved `GuiFrame` and
`GuiEvent` in the SDL bridge and GUI shell. The bridge had no owner import;
the types were declared in the app shell, which already imported that bridge.
The split shell render/core modules also duplicated the same record layouts.
Importing the app shell back into the library bridge would add a cycle.

Move the two plain records into `std.editor.common.gui_types`, keeping every
field, its order and type exactly unchanged. There are no added defaults or
runtime conversions. The app shell, split render/core modules and SDL bridge
now import the same nominal definitions. The app modules explicitly reexport
their original record names so existing API paths remain valid. The shared
owner imports no app module and owns no window, process or runtime resource.

The GUI shell also imports its existing configuration setter, dock constants,
wiki property form renderer/HTML escaper and preview renderer directly from
their established owners. Rendering/event bodies are otherwise unchanged.

Three executable cases check shell-to-shared nominal record compatibility,
empty/Unicode event payloads, and shell-frame-to-SDL DrawIR composition with
actual text/geometry assertions. The latter calls the existing composition
builder, not SDL window creation or presentation. All three cases are **UNRUN**.
Source layout/import checks do not qualify GUI behavior, the separate DrawIR
v4 contract gap, or the otherwise incomplete historical split shell modules.

Evidence: final full-CLI log SHA-256
`0850b659da9f5a612051ed073f9062414329818219bce1f96c3f044b6be01340`.
