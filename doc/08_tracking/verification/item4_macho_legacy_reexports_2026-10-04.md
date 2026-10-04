# Mach-O legacy reexport verification

STATUS: FAIL — complete SDK, Phase 4 and five-host execution remain unqualified.

This increment projects checked LC_SUB_UMBRELLA and LC_SUB_LIBRARY metadata,
matches normal/weak dependency records, and preserves their original ordinals.
All matches receive whole-library visibility; unmatched selectors are no-ops.
The documented Mach-O library stem ends at the first dot or underscore; the
design explicitly records differences from current ld64's matching quirks.

The no-reexports header flag suppresses legacy visibility without bypassing
string validation. Eligible classic providers can inspect a child's parent
umbrella using the physical owner name. Nonmatching probed children remain
inactive and are not lowered or subjected to deployment checks. Modern ordinary
dependencies are not newly probed. Existing modern reexports and aliases retain
their behavior. No hosted-default or admission-authority change is included.

Initial executable intent bf0ff4730f8 preceded production edits. Additional
controls and review regressions accompany implementation; no executed RED/GREEN
or claim that every regression preceded its fix is made. LLVM-built inputs and
documented command mutations provide independent format evidence only, not
Simple or Darwin execution or acceptance of mutated code signatures.

Core 89da96988ee and hosted guard c6dcb1f96bb/f77ad587503 received independent
source review without concrete P0/P1 findings. The guard requires a closure for
active legacy visibility while preserving classic providers without ordinary
dependencies. Selector indexes avoid nested selector-by-dependency scans.
Existing work/source/byte accounting remains logical, not a process-RSS or
bounded-allocation guarantee.

Both integration and shared bin/release directories were absent at this turn's
check. Simple compilation, SSpec, generated manuals, coverage, core/lib/MCP,
native host and performance checks remain UNRUN. No seed fallback or repeated
bootstrap diagnostic was used. Full SDK semantics, managed admission, broader
linker work and execution on all five requested hosts remain open.

Acceptance now includes nine scenarios in the main legacy suite and three in
the separate dependency-modes suite. The added all-matches case requires a later
dependency's real exports after the first match exports nothing. Other cases
cover both CPU selector paths, physical-parent inference, inactive high-minimum
children, malformed strings, exact stems, dormant metadata, present weak versus
lazy/upward visibility, matched-missing failure and unmatched-absent success.
Native image and destination-byte assertions exercise the production route.
These are authored tests, not execution receipts; present weak-provider coverage
does not establish absent weak-import or general SDK weak semantics.
