# Engine2D Vulkan device identity used a presence sentinel

Status: CODE FIXED, DEVICE EVIDENCE OPEN — found 2026-09-26.

Originally `rt_vulkan_get_device()` returned `1` whenever `STATE.device` was
present, so Engine2D receipts could not distinguish device generations. The
native runtime now returns a positive, monotonically allocated selection
token. The selected physical-device UUID query requires that token under the
same native state lock and rejects a changed or quarantined generation. The
Simple strict capture path passes its completed submission's token. Skia's
numeric receipt field remains an enumeration index, so numeric fields across
backends are still not comparable.

This closes the stale same-model device switch at the identity query. It does
not establish a physical Linux capture or authenticate caller-supplied pair
records. The physical pair contract remains `candidate` for matching pixels.

Remaining acceptance: verify the new native symbol in a deployed self-hosted
runtime, execute a same-model, different-UUID negative case, and collect a
physical Linux Vulkan capture. A caller-provided UUID string never promotes a
pair to PASS.
