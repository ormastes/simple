<!-- codex-research -->
# Domain research: SFFI v2 admission acceptance

**Date:** 2026-08-27

## Findings

1. Rust treats an `unsafe extern` declaration as a proof obligation at the
   declaration site because the compiler cannot validate a foreign signature.
   Simple should likewise require explicit raw-boundary ownership and test the
   lifting wrapper, rather than infer safety from symbol spelling.
   [Rust Reference](https://doc.rust-lang.org/stable/reference/unsafe-keyword.html),
   [RFC 3484](https://rust-lang.github.io/rfcs/3484-unsafe-extern-blocks.html)
2. SLSA provenance binds an artifact subject to build definition and run
   details. It supports artifact identity and reproducibility claims, but does
   not establish ABI/null/ownership semantics; acceptance must keep those
   verdicts separate.
   [SLSA provenance](https://slsa.dev/spec/v1.2/provenance)
3. Sigstore blob bundles carry signature, certificate, and transparency-log
   evidence. Verification must bind both digest and trusted identity/issuer;
   a self-supplied key beside an artifact is not a trust policy.
   [Cosign blob signing](https://docs.sigstore.dev/cosign/signing/signing_with_blobs/),
   [Cosign verification](https://docs.sigstore.dev/cosign/verifying/verify/)
4. The WebAssembly Component Model separates canonical lift/lower from core
   calls and gives resources explicit lifecycle operations. It is a useful
   model for Simple's generated typed wrappers: validate/lift once at the
   boundary, retain explicit resource ownership, and keep the hot path typed.
   [Canonical ABI](https://component-model.bytecodealliance.org/advanced/canonical-abi.html)

## Replanning consequence

The first acceptance surface is a fixture-driven admission runner with typed
outcomes. Modern SSpec invokes that runner and asserts both success and each
rejection class. Source audits remain supporting evidence only. Provider
implementation migration, signed CI bundles, and optional sandbox/Wasm lanes
follow once the acceptance contract is executable.
