# Streaming guard rejects a valid CLI entry before import discovery

Status: source fix and actual CLI regression supplied for the next producer.
End-to-end PASS on the refreshed producer is required and is not yet claimed.

Producer `399139d3ac143aa76e46212060583b4f8e449b7de53ae256185c99fe6052e6d3`
from frozen source `72f2d6a8e602bab910c309b4e93b41a521c316e8` immediately
rejected the Phase 3 invocation with `E-DRV-STREAM-ENTRY`, although arguments
contained `--entry-closure --entry src/app/cli/bootstrap_main.spl`.

`run_focused_native_build_plan` correctly parses and publishes the requested
entry in `SIMPLE_NATIVE_BUILD_ENTRY`. It deliberately sets
`SIMPLE_NATIVE_BUILD_ENTRY_CLOSURE=0` so the loader will discover that entry's
imports. The pre-load streaming guard introduced by `149fbbebf8e` accepted only
the completed closure latch or a compiler-owned entry configuration field.
This confused entry authority with completed discovery and rejected the request
before source loading could establish the latter.

The fix accepts `driver_source_entry_request(ctx)` as early entry authority,
or an already complete closure. It changes only the streaming gate. It does
not set the completion latch, weaken missing-entry rejection, skip discovery,
or remove the AOT/coverage/MC-DC/backend safeguards.

Actual candidate CLI negative controls are retained under
`/mnt/simple-bootstrap-6b2/streaming-entry-order-20260930/{named,positional}`.
Both named and positional routes returned exit 1 with the same entry guard.
The positional control initially hit SCV admission because the small fixture
was not a Git repository; it was then committed as
`cf371caa7f403190ce256cee4f7a269ef5bdc011` and reached the entry guard. No SCV
bypass or counterfeit closure latch was used. There is no proven positional
workaround on this producer.

The tracked fixture under `test/fixtures/compiler/streaming_cli_entry` contains
two files: the bootstrap entry imports a dependency returning 37 and verifies
the returned value at runtime. The executable Simple harness
`test/02_integration/compiler/driver/streaming_cli_entry_regression.spl` accepts
producer, runtime, committed fixture root, and fresh private cache root paths.
It invokes both actual CLI routes, requires successful compilation, exactly
two streaming release receipts including the dependency, an emitted executable,
and runtime output proving the imported value equals 37. It preserves all logs
and rejects an already-existing output. Run it against the refreshed producer
using a supported Simple test host; neither this harness nor its end-to-end
positive controls have passed yet.

The smaller policy regression is expanded from 22 to 29 cases, now using the
actual focused argument parser for both named entry spellings and checking the
entry-before-discovery state. The prior 22-case PASS belongs to the earlier
policy and does not qualify this new wiring fix.
