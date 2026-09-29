# WM browser event probe/validator drift

Status: source contract fixed; live production admission pending real receipts.

## Defect

`validate-wm-browser-event-routing-proof.js` required a production Aetheric
envelope, ordered WM/input events, sandbox and GPU identity, animation motion,
input-to-paint latency, font-frame correlation, and Electron package identity.
The checked-in `wm_event_check.js` had regressed to an older fixed-theme probe
that emitted only event counts and payloads. Consequently every real proof was
rejected with `event-routing-proof-source-marker-missing` before its behavior
could be admitted.

## Fix

The retained reviewed production-envelope implementation was recovered from jj
change `wmmskyylvlxp` (`dc78e6422f21`) and restored. The seven validator
requirements added after that revision are now implemented: sandboxed renderer,
GPU feature status, and initial/final CSS animation opacity and timeline motion.
The validator reports both proof-source file and artifact status `pass`.

## Remaining verification

A live admitted run requires non-synthetic `aetheric-host-web-gui-v1` evidence
and a matching pure-Simple font-composition receipt. Neither artifact currently
exists in the shared or known agent build trees, so no production pass receipt
was fabricated. The earlier direct Electron probe proved focus, move, maximize,
title command, text input, and pointer routing, but is not a substitute for the
full production-envelope gate.

An independent headful Chromium primitive run also proved a real scrollable
panel path: CDP delivered a trusted wheel event, the overflow container reached
`scrollTop=40`, pointer/keyboard/resize inputs were trusted, and the receipt
reported zero dropped events and no fallback. This complements the internal
window event probe; it is not presented as a single combined production proof.
