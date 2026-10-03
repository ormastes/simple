# Archive payload admission source handoff

Owner: item6_research. Branch: `work/item6-precise-routing-20261003`.
This follow-up commits separately from precise routing.

The prior warm archive owner checked the mapping and receipt, then returned a
CAS filename without verifying the actual archive. Missing, modified, or
hash-consistent malformed members could therefore be reported as cache hits.

`package_archive_load_v1` now fetches through checksum-verifying `cas_get`,
checks exact three-member names/order, contiguous coverage, nonzero bounded
spans without arithmetic overflow, UTF-8 and member hashes, canonical manifest
bindings, and existing interface/action symbol resolution. Corrupt or missing
payloads behind admitted mappings refuse with `source_required=false`.
Only absent mappings remain source-work misses. Receipt digest fields are
validated before they can become CAS paths. Aggregation/dependency ordering
uses the existing bytewise canonical sort owner.

`package_archive_payloads_v1` is shared with the retained cold helper. The cold
publisher uses the warm owner's already-admitted member digests without a
second CAS read or duplicate payload decoding. Existing cold semantic/UTF-8
diagnostic spellings are preserved. A returned path is not a lifetime pin;
downstream installation still must pin and revalidate against concurrent writes.
The package route retains each first validated load record for its immutable
request generation. Final routing reuses that receipt rather than rereading
every archive; later SCC dirtiness can discard a hit but cannot alter its
aggregate. The route fixture compares the returned receipt/path with the actual
admitted archive. No synthetic read-count API was added for the test.

The stale unit spec's removed publisher and nonexistent load fields were
replaced with actual SCC publication and aggregated-entry loads. Eight modern
examples include table cases for authority changes, missing/corrupt payloads,
forged offsets/names/overflow/digests/coverage, forged manifest identity and
invalid symbol/action grammar. Forged receipts use the real CAS mapping
transaction rather than a mock lookup. Native smoke and precise route fixtures
now supply real symbol/action rows instead of opaque placeholder text.

`app.test.package_index_acceptance_archive` exposes only actual archive owner
observations for package-archive-cache-hit and clean-warm-reproducibility.
The two adapter tests compare stored bytes and measured receipt/payload hashes.
No source-read, compiler-work, no-scan or codegen counter is invented. The
broader compiler scenarios remain unqualified by this adapter alone.

All executable tests remain UNEXECUTED without an admitted pure-Simple runner.
Source/import/whitespace checks are not RED/GREEN or native qualification.
Warm-hit hashing/decoding is necessary correctness work; production time/RSS
measurement is still pending. No performance improvement is claimed.
