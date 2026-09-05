<!-- codex-design -->
# GUI/SSR evidence design

The feature adds no administration GUI. Its UI surface is server-side rendering consumed by the Simple browser and external browsers.

The primary fixture contains text, font/style changes, nested layout, image/color content, interaction/hydration metadata, and a data-backed component. The server captures semantic HTML/composition and an Engine2D pixel readback. The Simple browser fetches the live response and captures its displayed result. Tests compare semantic invariants and independently generated pixel/golden diffs rather than accepting the server output as its own oracle.

Durable captures live under `doc/06_spec/image/03_system/app/ui_web/feature/secure_web_ssr_interop_spec/<case>/`; transient HTML, protocol, timing, and logs live under `build/test-artifacts/03_system/app/ui_web/feature/secure_web_ssr_interop_spec/<run-id>/`.

