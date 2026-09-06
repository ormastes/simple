# x86_64 Authenticated Media Cryptographic Round Trip

Run:

```sh
sh test/02_integration/os/x86_64_authenticated_media_roundtrip_test.shs --self-test
```

The self-test selects an admitted pure-Simple compiler, builds the lightweight
canonical-body helper with stub fallback disabled, generates an ephemeral
Ed25519 key pair, creates signed x86_64 hello media, and invokes the Simple
helper a second time. It requires the independently emitted body digest to
equal the admission digest and verifies the signature over those exact bytes.

If no admitted compiler and adjacent admission receipt are installed, the test
reports an explicit `SKIP`; it never substitutes the Rust bootstrap seed.
