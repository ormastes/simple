# Editor SDL dock tabs and panels have no spatial renderer

Status: OPEN. The GUI dock source repair models panel placement and emits zone-specific HTML, but native SDL visual docking is not implemented or verified.

`gui_shell.spl` and `gui_shell_render.spl` render dock tabs and panel bodies as HTML with pixel-sized zone wrappers. `src/lib/editor/70.backend/gui_sdl_bridge.spl` passes each `GuiFrame` HTML field as plain text rows to `gui_sdl_render_text_block` at fixed positions. It does not interpret the HTML/CSS positions, draw tab rectangles, or place moved panel bodies at their dock coordinates. SDL does emit mouse down/move/up coordinates, so the model can change while the visible SDL frame stays at its fixed text positions.

Required work: define a shared pixel rectangle for each visible dock zone and tab; draw the selected panel body and tab labels through SDL Draw IR at those rectangles; use the same rectangles for pointer hit and drop targets; verify left, right, and bottom movement at default and resized dimensions. The HTML frame spec alone does not prove native SDL visual behavior.
