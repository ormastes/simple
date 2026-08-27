# MCI-v2 SimpleOS collector

The script scripts/check/produce-mci-v2-simpleos-collector.shs finalizes one
selected SimpleOS host/QEMU row as the exact signed
simpleos-qemu-host-collector-v1 receipt consumed by
check-mci-v2-simpleos-manifest.shs.

The producer is a bounded receipt finalizer. Its bundle contains pinned
command text, target transcripts, payload identity files, and the image file.
In --mode live, each command runs through bounded timeout capture and must
produce a pure-Simple version result, a passing compile transcript, exact
hello world output, a non-empty resource series, and an all-pass invariant
ledger. Stress timestamps must span exactly 86,400,000,000,000 ns. Command
text and retained transcripts are hash-bound before signing.

Fixture use is explicit:

    scripts/check/produce-mci-v2-simpleos-collector.shs +      --mode fixture --contract-fixture +      --evidence build/evidence/mci-v2/simpleos +      --bundle build/fixtures/simpleos-collector +      --cell linux:x86_32 --run-id fixture-run +      --source-hash SHA256 --compiler-receipt-hash SHA256 +      --configuration-hash SHA256 --image build/fixtures/simpleos.img +      --collector-key-id fixture-collector +      --collector-private-key build/keys/collector.key

Fixture output prints mode=CONTRACT_ONLY. It is suitable for schema, signing,
and publication tests only; invoke the manifest validator with
--contract-fixture, and do not use its blocked result as release evidence.
Live mode forbids that flag and requires an operator-pinned signing key plus
real command/transcript/time/stress inputs. Missing, malformed, colliding, or
changed inputs fail closed.

Focused coverage is in
test/01_unit/scripts/mci_v2_simpleos_collector_producer_contract_test.shs.
