# Network text-session loopback scenarios

Authored manual, not generated execution evidence. All 23 cases are **UNRUN**. REQ-UTF8-EXTERNAL-TEXT-008. Setup uses real ephemeral IPv4 loopback sockets and 1000 ms timeouts.

1. retains a split UTF8 scalar and distinguishes empty decode from EOF.
2. handles split required BOM and UTF16 surrogate pairs for both byte orders.
3. latches truncated EOF and does not return a partial scalar.
4. rejects malformed input and latches its codec failure.
5. enforces forbidden BOM at stream start across split reads.
6. rejects oversized writes before bytes or BOM are committed and permits corrected input.
7. allows exact UTF16 byte limits without conservatively rejecting multibyte UTF8.
8. validates read limits before consuming a transport byte.
9. writes across bounded send windows without duplicating bytes.
10. keeps simultaneous session encodings isolated.
11. rejects operations after owning session close without accepting a raw alias.
12. owns connected and accepted transports without exposing raw stream aliases.
13. sends generic and packed binary arrays with identical exact octets.
14. emits a required BOM once even when the first write is empty.
15. keeps a forbidden BOM policy after empty writes and rejects malformed output before commit.
16. applies BOM and UTF16 policies independently to every datagram.
17. rejects truncated and oversized datagrams without poisoning the next packet.
18. transports an empty datagram as an empty message rather than stream EOF.
19. should observe TCP close through another reference to the same session.
20. should observe UDP close through another reference to the same session.
21. should decode exact ordinary UTF8 frames without consuming the following frame.
22. should reject malformed ordinary UTF8 output before sending any bytes.
23. should reject malformed ordinary incoming UTF8 instead of constructing internal text.

The executable spec contains exact byte/error assertions and valid traffic after admission failures. Shared-reference close cases do not prove resource moves, cloning, descriptor reuse or concurrent lifetime safety. Multiple send windows do not force native short writes. Allocation failure, late transport failure, runtime layout, platform and performance qualification remain open.
