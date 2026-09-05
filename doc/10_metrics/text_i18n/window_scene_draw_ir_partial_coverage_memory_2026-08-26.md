# Window-scene Draw IR partial coverage and memory diagnostic

Date: 2026-08-26  
Owner: `src/lib/common/ui/window_scene_draw_ir.spl`  
Status: **UNAVAILABLE / release-blocking**

The combined pure-Simple coverage run was terminated after more than four
minutes without progress. It returned exit 143, so its artifact is partial and
is not admissible proof of the owner's static branch denominator.

Nine completed specifications reported 60 passing and 3 failing scenarios.
The failures were the readable-bitmap source assertion, a composed-batch
containment assertion, and a stale no-snapshot compatibility hash
(`4292668155` versus `4293059302`). Other requested specifications did not
reach a verdict before termination.

The partial CSV contains 23 runtime decision records for this owner, each with
only one observed outcome. It cannot establish how many decisions in the
1,765-line source were never instrumented or reached. Whole-owner branch
coverage therefore remains unavailable, not 50% and not 100%.

The stuck process was observed near 147,056 KiB RSS (~143.6 MiB). This is only
a runner/module-closure diagnostic: it includes compiler, SPipe, imported UI,
font, browser, and rendering modules. It is not an owner allocation receipt.
Owner allocation count/bytes, retained scene/cache bytes, transient composition
workspace, atlas host bytes, staging/upload bytes, device-local VRAM,
post-eviction retention, and post-cleanup RSS are all **unavailable**.

Acceptance requires a bounded native harness around the canonical window-scene
projection/composition API, static-denominator branch instrumentation, and the
joint latency/allocation/RSS/cache/atlas/VRAM receipt defined by the performance
plan. Narrow smoke specs may diagnose behavior but cannot substitute for that
owner receipt.
