<!-- codex-research -->
# Windows Full Bootstrap and Toolchain Suite — Domain Research

## Provenance-Bound Promotion

SLSA provenance identifies where, when, and how an artifact was produced and binds an output digest to its build process. Its build requirements emphasize consistent production, digest-bearing subjects, and authenticated provenance distribution. Applied here, every Simple phase must record an immutable executable digest, source revision, command/environment, parent compiler, and admission authority; a path or success log alone is insufficient.

Sources: [SLSA Provenance](https://slsa.dev/spec/v1.2/provenance), [SLSA Build Requirements](https://slsa.dev/spec/v1.2/build-requirements).

## Reproducibility and Environment Capture

Reproducible Builds defines a reproducible build as the same source, environment, and instructions producing bit-identical specified artifacts, verified by cryptographic hashes. Its build-perimeter guidance makes toolchain and environment inputs part of the reproducibility boundary. The Windows lane therefore needs pinned MSVC/GNU/LLVM identities, normalized environment, isolated caches, stable source state, and exact artifact hashes before comparison or promotion.

Sources: [Reproducible Builds definition](https://reproducible-builds.org/docs/definition/), [Build perimeter](https://reproducible-builds.org/docs/perimeter/).

## Rollback and Mix-and-Match Resistance

The Update Framework treats rollback, freeze, mix-and-match, and wrong-artifact installation as distinct threats. A safe local deployment must reject stale or cross-generation files, switch one immutable generation atomically, retain trusted digest/version state, and make rollback an authorized receipt-producing transition rather than a directory copy.

Source: [The Update Framework specification](https://github.com/theupdateframework/specification/blob/master/tuf-spec.md).

## Evidence Retention

NIST SSDF SP 800-218 practice PS.3.1 calls for securely archiving release files and supporting data with integrity/provenance. Phase commands, environment, logs, hashes, receipts, checks, review status, and rollback evidence should therefore be retained together and referenced by the exact published commit.

Source: [NIST SP 800-218](https://nvlpubs.nist.gov/nistpubs/specialpublications/nist.sp.800-218.pdf).

## Domain Conclusion

The appropriate model is an immutable, digest-addressed promotion chain with separate build, test, admission, publication, deployment, and rollback authorities. Cross-host or earlier-phase success can diagnose problems but cannot substitute for an exact Windows subject tested at the phase being promoted.

