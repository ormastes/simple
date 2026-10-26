# Native source-slot ownership feasibility

Status: native primitive feasibility PASS; production integration and compiler performance remain UNRUN.

On Windows, an import-free Simple fixture compiled through the d958 bootstrap LLVM archive path and linked against the previously pinned strict core-C provider used by the final3 native fixture. This is a bootstrap diagnostic, not self-hosted compiler acceptance. Two bounded verification cycles executed one expected-negative control and six positive criteria; unchanged passing criteria were not repeated.

The negative control confirmed that clearing a 32-alias array does not reclaim its source allocation. The positive criteria covered:

1. Invalidating 32 aliases, copying the source, releasing the old source and array, and validating the independent destination.
2. Explicitly owned scalar text and exact registry-count cleanup.
3. A 317,440-byte UTF-8 destination compared byte by byte with an immutable seed after the original source was released.
4. Cancellation cleanup before copying.
5. Cancellation cleanup after copying and before adoption.
6. Empty and one-byte shared strings: refused frees preserve valid bytes and do not alter allocation counts.

The cancellation criteria exercise deterministic explicit cleanup branches, not asynchronous interruption or concurrent lease handling.

The first cycle's scalar setup incorrectly assumed `repeat(value, 1)` allocates. Inspection of the sealed provider showed it returns the original value. The second cycle corrected only the fixture setup and ran the five remaining criteria; all passed with exit 0. The already-passing alias case was not repeated. All nine child stages terminated with empty Windows Jobs, and input pins remained unchanged.

## Immutable evidence

SHA-256 pins:

| Artifact | Digest |
| --- | --- |
| Strict core-C archive | `9693a97f114da7fff53abf3abb4d03d0ac79b1d9dde899649d7c29f89e0cbccf` |
| Actual runtime object | `434a56ed3786fed4d072ae3791bd7c6f1b31de8c3c144480308014d2442ab328` |
| Preprocessed runtime input | `aab05a728f4497c851e4eebddae143f799b0dcbfc58866fcc38b78a04100c52d` |
| Baseline executable | `9e92406f3bfd2cb1c1e408ccf468175d6f8613f376870827e318d12fc89600b9` |
| First candidate executable | `1c4a5266d98ffcbc2526ccd7280f768c9fae26a353055aee1a2b32d2feb871ea` |
| Second candidate executable | `b5ebdba510790f236d3188d5b8f4f8895f132dad527faf812469e323d8ff76a9` |

The host-local evidence packet is `build/native_probe/source-slot-native-feasibility-20261012/`: `REVIEW.md`, both cycles' final pins, collector receipts, fixtures and link maps. Link maps bind copy, free, registry and byte access to the pinned runtime object. These host artifacts are not distributed by this documentation commit.

The second cycle's build/link/run collector intervals were 0.751002/0.327976/0.270930 seconds, with sampled peak RSS 81,384/41,408/3,460 KiB. CPU time was not collected. These are fixture measurements; they do not establish compiler latency, a 0.1-second compilation target, payload-byte bounds or production RSS savings.

## Production acceptance still required

The current driver copies text into a canonical streaming owner while retaining old `SourceFile.content` aliases. Its fingerprint reads those aliases, preparse reclamation frees their old content, and later streaming reclamation frees the canonical copies. Removing a copy or release independently can create a use-after-free.

A production repair must establish one authenticated physical source owner, retire scanner loans, redirect every alias, preserve fingerprint bytes and module order, distinguish transferred rows from legacy independently copied rows, and drain cancellation paths exactly once. Final canonical-owner reclamation must remain the sole free for adopted text. Shared strings require explicit handling; allocation length or an ownership enum does not prove exclusivity.

The primitive probe changed no production source. Full-driver integration, native ABI checks, cold/warm cache behavior, worker sharing, regression tests and performance qualification remain pending. No Phase 3 compiler, Phase 4 executable suite or six-binary subsystem test completion is implied by this PASS.
