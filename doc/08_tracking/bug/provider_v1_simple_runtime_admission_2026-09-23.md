# Provider V1 Simple runtime admission is not yet verified

Status: OPEN. The canonical 84-byte V1 result/full SHA-256 digest source contract is restored, but no pure-Simple provider query/invoke PASS is claimed.

An actual C shared-library host check passed query and invoke and rejected a historical 60-byte writer. The production Simple wrapper now poison-fills the 84-byte result so partial writers cannot inherit zero-valued reserved bytes. Source review found the 44/84-byte layout coherent; it did not establish Simple runtime behavior.

The focused four-module native driver/wire probe built and linked with the admitted Stage 2 compiler from `D:/b424fresh` (SHA-256 `510d70d22d0e909e04bb0f6e37087cea8c1fa1e0af6c8e89340db08b7168f7eb`) but returned exit 3 at `encode_provider_query_result_v1`, with no diagnostic text captured. Three bounded cycles were exhausted. Evidence: `build/mini_builds/core-provider-dispatch/HANDOFF.md` and its `driver-cycle*.log` files in the publication checkout.

A focused native test of the production `call_provider_query_v1` wrapper could not link: its generic dynamic-library import closure requires unrelated kernel VMM symbols. Evidence: `build/mini_builds/provider-abi84-host/HANDOFF.md` and `wrapper-build.log`. Do not count the C host check as a Simple runtime or Windows IDE dynload PASS.

Required follow-up: localize the wire encode failure with a semantically valid, no-stub focused executable; verify the production wrapper against full 84-byte and partial 60-byte writers; then execute the owned provider dispatch query/invoke/release/close path with an SCI-locked artifact. Do not relax the digest or reserved-byte checks to make a probe pass.
