# Simple Browser Chromium HTML Parity - NFRs

Feature: `simple_browser_chromium_html_parity`

- NFR-001: Default parity runs must not launch Electron; they must load checked-in Chromium PPMs.
- NFR-002: The acceptance budget is perceptual match `>= 9900/10000`.
- NFR-003: Regeneration must be deterministic in artifact paths: `chrome.ppm`, `simple.ppm`, `diff_chrome_vs_simple.ppm`, and `report.sdn`.
- NFR-004: Pure HTML rendering must avoid Engine2D backend startup in the parity path.
- NFR-005: Diagnostics must be suitable for CI logs and identify the first divergent fixture.
