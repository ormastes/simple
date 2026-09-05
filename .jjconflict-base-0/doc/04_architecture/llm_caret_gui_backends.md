# LLM Caret GUI Backends — Architecture

## Ownership

`llm_caret` owns prompt state, dummy dispatch, semantic HTML, and launch intent.
`gui_electron.spl` is the Caret-side host adapter; `ui.electron` owns
`BrowserWindow` transport. Simple Web owns HTML/CSS parsing,
layout, and Draw IR emission. Engine2D owns Metal execution and device readback.
winit owns the native window/event transport.

## Flows

Electron:

`caret --electron -> Caret HTTP server -> Electron --url -> DOM action ->
POST /api/chat -> dummy provider -> hello`.

Pure Simple Metal:

`winit key event -> Caret reducer -> dummy provider -> semantic Caret HTML ->
Simple Web layout -> DrawIrComposition -> Engine2D Metal -> device readback ->
winit present`.

The native adapter fails closed unless the Draw IR composition is non-empty and
the resolved backend/readback prove real Metal execution.
