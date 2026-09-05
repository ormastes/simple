# Full compiler check shows no progress for more than five minutes

**Date:** 2026-08-21  
**Status:** Open  
**Command:** `bin/simple check src/compiler`

During SFFI function-pointer hardening, the required full compiler check emitted
no result or progress for 5 minutes 55 seconds and was terminated to honor the
repository runaway guard. The focused checks for every changed Simple file had
already passed. The command was run through the repository `bin/simple`, which
warned that the deployed executable is currently a Rust bootstrap seed rather
than the required pure-Simple production tool.

This is not evidence of a correctness failure in the SFFI change, but it is
also not a PASS. A follow-up should identify whether the time is spent loading
the full compiler tree, resolving duplicate modules, or checking files that are
outside the entry closure. The check should expose bounded progress and a
measured warm-run target so release verification cannot hang silently.

No retry was performed in this session.
