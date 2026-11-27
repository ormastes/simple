# smux session messaging

Authored manual for `test/03_system/tools/smux_session_messaging_spec.spl`. Status: TEST_BLOCKED; no actual Phase 3 execution or generated-manual receipt.

| Scenario | Steps and actual oracle |
|---|---|
| Session discovery | Create two service sessions; list IDs/names; preserve count-only list reply |
| Stable resolution | Create duplicate names and a name equal to another ID; refuse ambiguity and select exact ID |
| Recipient scope | Attach clients to two sessions; authenticated Unicode notice appears only for the selected pair |
| Authority | Wrong token and an extra claimed-sender field cannot enqueue |
| Peek/ACK order | Repeated reads retain the oldest ID; out-of-order/cross-recipient ACKs refuse; correct ACK exposes the next item |
| Queue capacity | Fill 32 actual records; overflow refuses without replacing the oldest; ACK frees capacity |
| UTF-8 bounds | Accept 256 emoji (1024 bytes); refuse overflow, empty bodies and malformed/partial scalars |
| Detach and resize | Same-session resize preserves notices; actual detach clears only its recipient; sibling notices survive |
| Rebind/reset | Moving an attachment clears its former queue; reset clears records without reusing message IDs |
| Safe rendering | Decode the real wire reply; C0/C1 payload controls cannot become terminal sequences; clipping preserves whole wide cells |
| Pane ownership | Wrong-session window/pane targeting refuses without changing either session focus |
| Reply classification | Accept exact none/envelope/queued/ACK forms; reject malformed payloads, IDs and extra fields |
| Actual Windows pane command | Spawn cmd.exe through ConPTY, detach, select another window, send two explicit commands to the original pane, require child-computed 5859 and unchanged focus |

The first twelve cases use actual production state, dispatchers and helpers; they do not simulate sockets or console success. The final case requires Windows and a real native PTY provider, with bounded capture polling and teardown before result assertions. A separate outer watchdog is still required for native process resources.

The notification render helper test proves generated output content, not actual screen pixels, successful console writing or acknowledgement timing. Those require the integrated native client fixture. The command test polls captures and therefore does not prove unattended background draining. Neither case establishes per-user sender identity: the server uses one shared authorization token.

Run only with the root-selected admitted Phase 3 producer and ordered Windows native provider roots. No execution count, doc generation, coverage percentage or runtime PASS is claimed in this manual.
