# LLM Caret GUI Backends — Detail Design

`main.spl` adds `electron` and `metal_gui` UI modes. Electron mode starts the
existing Caret HTTP listener and delegates canonical-shell discovery/spawn to
`gui_electron.spl`, which supplies the Caret URL, title, dimensions, and
optional local debugging port. Metal mode delegates to `gui_metal.spl`.

`gui_native_model.spl` contains pure prompt editing/submission reducers. Enter
returns a submit action; response application clears the prompt and stores the
user/assistant turn.

`gui.spl` adds a static semantic HTML producer for the native renderer.
`gui_metal.spl` verifies Draw IR, resolved backend, device readback, pixel count,
handle/identity, and checksum before presentation. It logs key/submission/frame
evidence for system driving.

Errors are visible and return nonzero in headless mode. A live window remains
responsive until close/Escape.
# Production Electron launch resolution

Caret and DevHub use the shared `app.ui.electron.app_launcher` capsule. The
capsule fails closed unless both the managed Electron package manifest and an
executable are present, always supplies the resolved application directory to
Electron, and searches at most six executable ancestors after checking the
current workspace. A process spawn alone is not rendering proof; the live GUI
system gate must still validate Caret-specific visible text and trusted input
delivery.
