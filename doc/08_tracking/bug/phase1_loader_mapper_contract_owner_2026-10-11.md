# Phase 1 loader mapping contract owner repair (2026-10-11)

REQ-PHASE1-LOADER-OWNER-001: the mapper public-surface source contract must follow
its native adapter to the executable-memory owner and preserve RW-to-RX and
no-RWX assertions across that boundary.

The retained mapper contract reported 4/5 passing cases. The current release
source reproduces the same single failing scenario with the cached bootstrap
producer: the nested native module delegates protection changes to the sibling
owner, while the spec still searches for obsolete local `val prot` expressions.

The repaired spec checks the actual import aliases and delegated allocation and
protection calls, then checks RW allocation and RX protection in
`src/compiler/99.loader/smf_mmap_native.spl`. It forbids RWX expressions in both
the adapter and owner. No production implementation or public API changes.

Diagnostic evidence: `build/phase1-loader-contract-20261011/baseline-result.json`
records 5 executed, 4 passed, 1 failed, exit 1. `check-result.json` records
5 executed, 5 passed, 0 failed, exit 0 (0.75 seconds). The six exact release
product source files and fixed spec are hash-bound in `source-binding.json`.
Producer SHA256: `15102d32226b3fbead63d3c63e33e99a6f0e9ffcddea06080fb65872445cbafb`.
The std library remains the retained frozen Phase 1 library. No compiler rebuild,
cohort replay, or repeated passing check occurred.

STATUS: PASS for the focused cached bootstrap diagnostic; pure-Simple runtime
qualification and the overall Phase 1 compiler/interpreter/loader/backend gate
remain unverified. This change does not qualify a release or publish artifacts.

Release sync: fetched `d7426dd5199a7d920dece4dd290c2160d2b9859f` after the
focused check. All six checked product-source SHA256 values are unchanged
from baseline `475c2f918db54a83cb30025fdf3610aea4cb2625`; passing evidence
was preserved without replay.
