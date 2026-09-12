# Windows bootstrap admission depends on unavailable `cmp`

**Date:** 2026-09-09  
**Status:** In progress; source fix and focused coverage are present, but the latest focused invocation exposed a test PATH fixture issue; host provisioning and a post-fix bootstrap proof remain open

The MSVC bootstrap reached private Rust authority admission and failed at
`bootstrap-from-scratch.sh:2597` because the canonical MSYS2/Git PATH contained
no `cmp.exe`. The host's ambient MSYS2 installation does provide
`/usr/bin/cmp` from GNU diffutils 3.12, and the host configuration now
declares the canonical MSYS2 utility directory explicitly; the applied
admitted PATH still requires proof in the bootstrap run and must not silently
inherit an ambient copy.
The admission lane used bare `cmp -s` at multiple provenance gates without
binding or diagnosing that prerequisite.

The Stage 3 authority now exposes a shared `bootstrap_stage3_compare_files`
helper with cmp-compatible statuses: 0 equal, 1 different, and >1 for missing,
unreadable, or unavailable comparison. The bootstrap admission/provenance
sites use this helper, and `cmp` is included in the canonical tool-authority
inventory so absence, ambient-path mismatch, symlink substitution, or hash
drift fails early with an explicit binding error. Remaining evidence is the
applied admitted PATH and one successful post-fix bootstrap admission; no
build/cache admission has been granted.
