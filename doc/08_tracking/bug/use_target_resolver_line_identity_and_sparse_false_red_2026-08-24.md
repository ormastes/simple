# Use-target ratchet keys line numbers and silently scans missing sparse files

**Date:** 2026-08-24
**Status:** CHECKER AND SOURCE DRIFT FIXED / BOOTSTRAP ADMISSION PENDING
**Owner:** must-check bootstrap lane

## Defects

The enforced baseline compared full diagnostic rows, including `path:line`.
Inserting unrelated lines changed the identity of unchanged debt and produced a
NEW plus STALE pair. Ratchet identity is now class, source file, target module,
and member; current line numbers remain diagnostic output. Identical repeated
debt within one file is one semantic obligation.

The scanner also used `git ls-files` without proving those paths existed in the
working tree. In a sparse checkout it indexed absent targets, `getline` returned
no content, and thousands of valid members became false MEMBER_MISSING rows.
Tracked-but-unmaterialized input now returns ERROR with the first missing path.

## Evidence

Thirteen fixtures pass, including real missing module/member cases, line-only
movement stability, changed-target distinction, vendor exclusion, non-vacuity,
missing tracked bytes, bare sibling imports, one-hop wildcard facades, and an
importer-scoped compiler-Rust stdlib root that cannot leak into the repository
stdlib namespace. The sparse checkout fails closed at the first absent
formal-verification spec instead of printing fabricated debt.

After materializing the complete `src/` and `test/` trees, the authoritative
scan checked 312,041 uses in 55.50 seconds/581,780 KiB and found 16 new plus 33
stale semantic rows. The earlier sparse result of 53 new/16,566 stale is invalid
and retracted. The baseline was not regenerated: the remaining rows require
source/alias review, including new warning-phase lint exports, raw file-read
imports, and bare sibling imports in `app.leak_finder`.

The follow-up authoritative scan checked 313,713 uses in 42.03 seconds with
623,708 KiB peak RSS. Every one of its 134 changed enforced keys was proven to
map to pre-existing debt (whole-module alias normalization or a more precise
MODULE_MISSING to MEMBER_MISSING classification); there were zero unmapped new
obligations. The corrected resolver made 3,960 old keys stale, and the baseline
was regenerated from the captured scan only after that mapping audit.

The source review also repaired real drift exposed by the stronger resolver:
canonical file reads in four bootstrap specs, split tooling and JSON owners,
real filesystem result handling, synchronous webhook transport, a missing
ctype smoke table, and an unused nonexistent time import.

At 42.03 seconds and roughly 609 MiB, this remains a bootstrap-owned gate and
must not move into the approximately ten-second push path. The bootstrap ledger
row stays TODO until an admitted Stage 4 bootstrap retains a clean scan.
