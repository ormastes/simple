# Remote container byte staging on actual filesystem fixtures V2

Status: **AWAITING_VERIFICATION** — source-authored specifications and manual.
No compiler, seed, test runner, filesystem scenario, provider, or container was
executed to qualify this artifact. No runtime PASS or coverage is claimed.

Source: `test/02_integration/app/buildrunner/remote_container_stage_v2_spec.spl`.
Implementation: `src/app/buildrunner/remote_container_stage_v2.spl`.

When run, each scenario creates a unique secure temporary fixture root containing
actual binary producer data, source text, and a binary declared input. SHA-256
digests are computed from those bytes. Owned roots come from the stager's reserve
API. All symlink targets and outside sentinels remain inside the private test
fixture root, which each completed scenario removes. Symlink scenarios require
host capability and assert setup success; unsupported setup is not a test pass.

| Scenario | Intended executable filesystem assertion |
| --- | --- |
| Cryptographic nonce pin | The real random provider reserves canonical 64-lowercase-hex-plus-LF bytes through an exclusive host claim; a second claim rejects without replacement. The returned bytes are hashed into a declared nonce input and copied/read back exactly by the actual stager. |
| Fresh-root nonces | Independent owned roots receive distinct canonical cryptographic nonce payloads. No deterministic substitute is used if entropy is unavailable. |
| Root reservation | Two reservations produce distinct real directories before any claim or manifest exists. |
| Exact byte staging | An exactly sufficient producer-plus-input budget admits staging; producer/input bytes and readback hashes match, canonical task manifest matches, output parent exists while output starts absent, and later source mutation cannot change copied bytes. |
| Exclusive claim | A second stage attempt rejects without overwriting previously admitted bytes, even if source bytes changed. |
| Producer mutation | Changed producer bytes reject before manifest publication; the failed root remains claimed and cannot be retried after restoration. |
| Input mutation | Changed declared source bytes reject before manifest or mutated input publication. |
| Byte bounds | Zero and over-1-GiB budgets reject before claiming; a one-byte-short cumulative budget rejects after earlier exact copies but before the final input or manifest. |
| Leaf no-follow | Producer or input symlinks reject even with correctly matching target digests, leaving the target unchanged and no manifest. |
| Root/parent no-follow | A symlink owner root or source parent rejects before any stage claim. |
| Output-parent escape | A symlink output parent rejects without creating outside directories or changing its sentinel. |
| Output-leaf escape | Live and dangling output symlinks reject through exclusive leaf reservation; outside sentinel bytes and absent target remain unchanged. |
| Existing regular output | A preexisting regular output rejects without replacing its content. |
| Invalid paths and links | Output traversal and a valid typed-link task reject before claiming; the portable stager does not flatten links. |

The producer fixture is arbitrary binary data and is never executed. Byte
staging does not establish executable permissions, Windows ACL admission,
container workspace ownership, native lifecycle success, or authority to launch.
Platform workspace/executable preparation and all container effects belong to
the Simple Container API provider. These filesystem assertions remain unrun.
The nonce cases require the actual cryptographic provider. Entropy absence
cannot produce a successful fixture or acceptance result; runtime qualification
remains **NOT_RUN** until the admitted runner executes these assertions.
