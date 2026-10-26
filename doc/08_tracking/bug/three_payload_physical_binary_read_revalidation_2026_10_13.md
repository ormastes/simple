# Three-payload binary read and reconstructed-carrier revalidation

2026-10-13 — **HOLD.** Provisional bug ID:
`three-payload-physical-broker-binary-read`. Qualified bug database reconciliation
is pending. No production fix or native test product is qualified by this report.

The frozen source is `cce267e717684e7f87aea1603df3da7c0745258d`.
The explicit Phase1 diagnostic producer is SHA-256
`d95807daf8725254e6737f12b0a81965ac5ae0a9236b19eedac94940bd9867f1`.
It executes original compiler/library owners through the canonical single-test
runner in an immutable source capsule. This does not attest the execution
engine, a rebuilt producer or native parity.

## Confirmed text/binary boundary defect

`src/compiler/80.driver/cache/worker/three_payload_physical_file_broker_v1.spl`
uses the bounded no-follow **text** reader, then converts its result to bytes.
A genuine encoded initializer TLD is 93 bytes with SHA-256
`63fe1fdd50d46bf8d9223b700144bb5ab77024cff7dd65a0d11d1052606c6a26`.
It contains invalid UTF-8. An actual focused provider check proved that the
text API rejects it and the byte sibling returns exactly those bytes/hash.
The same invocation's separate corruption oracle failed; the whole invocation
was not a PASS.

The private three-line candidate changes only the facade import/call and
removes text-to-byte conversion. Bounds, no-follow admission, error mapping,
seal/digest verification and the confined worker remain intact. Its patch is
SHA-256 `60829ae51ad2602ddcde33272adb37f00d7c68c40509af2c09debed08035dd0b`.
No shared production owner was edited.

## Actual bounded repair evidence

The broker feature used three invocations and is now closed/HOLD:

| Invocation | Actual named cases | Result |
|---|---:|---|
| Candidate broker | 6 | 3 passed; cold, warm and nonASCII positives failed |
| Cold stage diagnostic | 1 | Failed; rejection localized before object allocation |
| Cold predicate diagnostic | 1 | Failed; reconstructed prepared verifier rejects |

These are eight case executions, including repeated failed cold diagnostics,
not eight unique original suite cases. The three successful corruption
rejections (empty, truncated and same-length modified initializer) were not
rerun. All three invocations ended with final Job membership zero. Peak RSS
was 582008, 583448 and 583700 KiB respectively.

The final actual trace proves:

- The original packer carrier passes its public verifier. Original seal,
  source and initializer hashes agree; actual index/object decoders succeed.
- The repaired physical broker reads source length 28 and initializer length
  93 and enters the real confined worker.
- Both compared seals are valid with identical digest, total 121, section
  count zero, maximum decode 121 and nine coverage roots.
- Reconstructed source/init hashes and carrier seal digest equal the original
  expected values; all prior roles are absent and reported header fields agree.
- `verify_prepared_three_payload_v2` nevertheless returns false for the
  reconstructed carrier. The existing guard returns `CorruptPayload` before
  allocating an object broker. Its inner rejecting condition remains unknown.

This does not attribute the failure to the unrelated semantic binder, SOSIX,
array mutation, a runtime representation difference or compiler lowering.
Those require new causal evidence. No validator is relaxed, no seal is
rewritten and no fourth invocation is authorized by this report.

All diagnostic owner paths were observed; canonical duplicate broker/formal/
worker owners were not observed. Source pins and scoped boundary inventories
remained unchanged, with no outside source paths observed. Existing read tracing
does not attest every consumed byte or transient filesystem write. The canonical
consumer deletes its raw structured case file; retained reader observations and
named verdicts are not described as an authenticated retained raw case receipt.

## Durable evidence

Packet relative to `build/native_probe/phase1-current-whole-20261012-sol/`:
`three-payload-owned-api/binary-broker-repair/`.

| Artifact | SHA-256 |
|---|---|
| `cycle1/FINAL_SEAL.json` | `b6d0b1db171f1e23b4e1efa2acc0eaf6a3ade3f3ce7292ffcd932b89769897b6` |
| `cycle2/RESULT.json` | `658d407e7497ad35932f822f882bfe3dd1f12a5c3d29c93d57363ac6e17b7272` |
| `cycle2/attempt/receipt.env` | `ddf1691694055d97a60aadaed5616324f4f5e1af5ac5daa1d8ab84a0d4f56853` |
| `cycle3/RESULT.json` | `86e0405b9d83327fd620b778d5505d435fef54451efabd9886d6f7bad7b7e339` |
| `cycle3/attempt/receipt.env` | `76ce99e12a4fdd1db3fa79ae07f4ed8b399230a8d88b72280354ed3949ece639` |

The separate source-plus-TLD aggregate binder mismatch and worker-availability
oracle disagreement remain open. Capability availability is not evidence that
a worker executed. Shared Simple byte consumption is the proposed repair;
Rust/native runtime parity remains unrun. The requested six Phase2 native test
products remain **0/6 qualified**.
