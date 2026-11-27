# Focused SDN chunk evidence

`writer-red-final-tests.log` is the authoritative red reproduction: the final selftest text with only the production append/ environment functions restored from 046c85. `red-test-identity.sdn` binds command, hashes and exit1. `writer-green.log` executes the repaired owner. The earlier warning-bearing red log remains in /tmp/p2-claim-intake-20261108/writer-red.log as historical evidence; it is not the final test identity.

`shape-red-final-guard.log` executes the final guard against the exact original database blob; identity receipt binds both hashes and exit1. `shape-red.log` is the initial two-orphan diagnosis. The final shape scan includes four actual own claim-history rows as well as the new primary and description. Initial strict table-shape11176 predates those two actual claim events and is retained as historical scoped evidence, not asserted to be a final-row-count check.

`seal-identity.sdn` binds the final database SHA256 and direct native XXH3 sidecar comparison; the input has no CR bytes. `claim-check.log` confirms the new pending record has actual owner/start/check history. `preservation.sdn` records exact row-multiset and inverse-byte preservation proof: only two original nativeall rows move, six new own tracking/history rows are authored; no foreign status changes. Full Simple loader execution remains UNRUN.

## Draft transposition onto current release

The final implementation blobs from f69b8c2e93aa8029d0027e62e3c7809c80fb2385 are unchanged on actual release0247364fa1ad6b5818b24da451034ca6cf507e42. That base includes runtime PR7843 and the external duplicate-check changes. No other database bytes or statuses changed: only the current two nativeall orphan rows move verbatim and six own registration/history rows are inserted. The recomputed single sidecar is9a8d7e775c1969f0, directly checked with native XXH3. Fresh shape scan passes11183rows. Historical writer green/red results are reused through unchanged source identities rather than rerun.

Final independent review remains UNAPPROVED: Opus refused the last attempt because its monthly spend limit was reached. This packaging is a draft for genuine CI; it authorizes no merge.
