# Nested verification campaign escapes the bootstrap session

The f57c Phase2 compiler linked successfully (3 compiled,1290 cached,0 failed).
Both frontend sanity modes, receiver probe and native planner passed. Starting
the mandatory compiler matrix caused the outer watchdog to exit90 with
bootstrap-session-escaped and unexpected process IDs16735,16740. The campaign
unconditionally unset the inherited session contract and started a new session.

Select inherit when either contract field exists. The watchdog validates both
fields and parent admission; partial/malformed contracts remain refusals.
Standalone campaigns still create a session. RSS limits and deadline are unchanged.

Actual standalone and nested watchdog tests passed under the focused fixture:
/root/item5-campaign-session-regression-20261013. Nested session IDs matched,
unexpected PID list was empty, and both receipts were complete/quiescent.
The tracked regression reproduces these cases. Full matrix and Phase3 are pending.
Retained failed attempt: /root/simple-block-repair-canonical-reserved-20261012/
stage2-source-refresh-f57c1c90539. Never override or relabel its exit90 receipt.
