# Signed preparation through the actual host owner

Status: **NOT_RUN**. Seven authored executable scenarios use real Ed25519
signatures, private files and the existing capacity journal. No provider effects
or platform qualification are implied.

Source: `test/03_system/app/orchestrator/feature/host_signed_prepare_spec.spl`.

| Scenario | Expected evidence |
|---|---|
| Exact replay and reopened writer | Identical receipt, no duplicate journal event, capacity charged once |
| Corrupt approval and expiry after signature validation | Exact rejection, no reservation payload directory or capacity mutation |
| Oversized UTF8 and noncanonical packet | Bounded decoder rejects before admission |
| Changed service fence, prepared and executing rows | Ordinary reopen rejects; quarantine keeps capacity charged and old receipts unusable |
| Separate helper actions and execution | Normal route refuses helper envelope; helper execution remains charged and cannot expire |
| Unconsumed helper expiry | Cancels only the prepared helper; normal envelopes do not enter helper admission |
| Mixed normal/helper journal | Both rows reopen with exact shared charges; zero CPU or memory helper refuses |

The three helper scenarios exercise trusted capacity primitives. They do not
claim signature/parent-budget verification by the pending helper service consumer.

Execution logs, compiler identity and branch coverage remain unavailable until
the admitted-runtime verification gate is run.

Additional authored NOT_RUN case: three sequential real journal preparations are expired and their physical capacity reused; after a new service fence, quarantined open succeeds with all three uncertain and availability refuses capacity-exceeded. This prevents recovery from being blocked before actual no-effect reconciliation. It does not itself prove native inventory or ready transition.
