# WebSocket masking entropy and propagation

**AUTHORED_UNRUN.** Twelve SSpec examples were authored before implementation.
Zero examples have recorded runtime execution; TDD is incomplete and coverage
is UNMEASURED. This manual is authored, not generated from a passing run.

Source: `test/01_unit/lib/nogc_sync_mut/websocket/websocket_mask_entropy_spec.spl`

SHA-256: `e83b8a0c61e27bd08aa74d7cb1903901a0256b0596965441e57be56141d0258c`

Primary standard: [RFC6455](https://www.rfc-editor.org/rfc/rfc6455.html), sections
5.1 (client/server masking), 5.3 (fresh unpredictable 32-bit mask from strong
entropy), 5.7 (published masked Hello wire example). Cached RFC text SHA-256:
`765775326aee0ecca9b04bde3fd1f52932d498e33e34e428bd61b8a24da0fa3b`.

| Examples | Oracle |
|---|---|
| Binary key conversion | 00/7f/80/ff survive exactly |
| Provider error and 0/3/5-byte results | Error, no fallback key |
| RFC Hello | `81 85 37 fa 21 3d 7f 9f 4d 51 58` |
| Mask error at encoder | Error, no frame value |
| All-zero valid random key | Legal key; payload unchanged by XOR |
| Server frame | Unmasked bytes, no entropy needed |
| Malformed key result | Reject non-four-byte key |
| Text/binary/continuation/ping/pong constructors | Exact unmasked wire bytes |
| Close constructors | Empty close and status 1000 wire bytes |
| Fragment constructors | Complete ordered frame collection in Result |
| Production RNG call | Four octets in byte range; not an entropy-quality proof |

The fail-closed error contract is repository policy enforcing the RFC entropy
requirement. Injected Result errors test the production conversion/encoder
boundary, not an actual OS provider failure or socket write. No runtime no-send
claim follows from these examples. No collision/uniqueness assertion is used.

Public API migration: mask generator, nine entropy-owning frame builders, three
close builders, two fragment builders, and CDP mask/frame builders now return
Result. CDP drain_events returns Result. Existing async facades transparently
reexport those signatures, so external callers must handle errors. Explicit-key
create_frame retains its existing API. Unmasked server paths bypass RNG.

CDP send/send_on_session return before write/pending insertion on key error.
Pong/close errors close the socket, mark closed, and return false; pump stops on
closed, and public pump consumers report transport errors. Electron close still
cleans up its process before propagating a false CDP-close result. Fragment
construction returns Err without exposing a partially built collection.

Remaining verification is specified in
`doc/03_plan/sys_test/websocket_mask_entropy.md`. The canonical entropy bug remains
OPEN pending actual runtime/provider/caller evidence. The implementation does
not intentionally retain a timestamp, empty-key, or panic fallback.
