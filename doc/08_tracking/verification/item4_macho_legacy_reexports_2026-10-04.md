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

Final independent source review binds main acceptance 006e145c405 and manual
7052901d52d, modes 9a4e14a9eb4, core 89da96988ee and the hosted guard commits
above: no concrete P0/P1 findings. Scoped whitespace, direct-env working/staged
and numbered-artifact checks passed against release base
487d64cfac314787e89c8bb7304e0a24eae3d450. The tracked doc/06_spec tree contains
zero executable specs; this increment adds only Markdown manuals there.
Subsequent review/report changes are Markdown only.

Committed test-tree delta passed with 3152 inherited offenders and zero new
offenders. Retained list:
`C:/dev/simple/.git/item4-macho-legacy-reexports-preexisting-offenders.txt`.
SHA256: `2fb68a47bab7953e058a449562ecba2df9f135b8d2e2d99c3e14f373b1c1d719`.
This scope result does not convert the inherited full-tree failure or any
UNRUN runtime/host gate into PASS.

Before landing, release advanced to 12e6a0362cf7d9bd84ec72a796ecfe9ce099312f
with 54 SSH/crypto repair paths and no owned-path overlap. Rebase preserved all
18 patches exactly (`range-diff` equality). The committed test-tree delta against
that new base also passed: 3152 inherited offenders, zero introduced. Its list
is `C:/dev/simple/.git/item4-macho-legacy-reexports-final-preexisting-offenders.txt`,
with the same SHA256 above. Source checks were not rerun for unchanged patches.
