# Supplemental pinned cryptographic sources

Status: SOURCE_ACQUIRED; no execution or conformance claim. Retrieved 2026-11-03 UTC. Cache and no-overwrite acquisition contract: [sources.md](sources.md).

SQLCipher v4.6.1 resolves to commit `c5bd336ece77922433aaf6d6fe8cf203b0c299d5`
(annotated tag object `fef10de5dfe3b2a0f740020d605636d4cc206c28` is not a content
commit). The official design/API webpages are date-and-content-hash snapshots;
they have no published immutable page revision. Source code carries its upstream
copyright/license header; webpage text is summarized, not reproduced wholesale.
RFC texts retain IETF copyright notices; NIST publication rights caveat remains
as in the main manifest. No full transcription is published here.

SQLCipher profile anchors: `sqlcipher_page_hmac` serializes page number according
to configured byte order, and `sqlcipher_page_cipher` authenticates ciphertext
plus IV before decryption. Tests targeting the v4 default LE profile must state
that profile, rather than asserting every SQLCipher configuration is LE.
`HMAC_SALT_MASK` is 0x3a and `FAST_PBKDF2_ITER` is 2; key derivation uses a
separate salted HMAC key. Pin page size, KDF iterations, algorithm, reserve-byte
layout and endian profile explicitly when constructing independent page fixtures.
These settings belong to SQLCipher, not to the abstract AES or PBKDF2 standards.

NIST SP 800-38A (December 2001), section 6.2 defines CBC; Appendix F.2.5/F.2.6
provides AES-256 CBC encryption/decryption vectors. Block-aligned NoPadding is
the selected caller contract; the NIST mode does not itself specify a universal
API padding policy. Local PDF extraction completed for all 66 physical pages in
`sp800-38a.extracted.md`; verify equations in the original before oracle copying.

RFC 8018 section 5.2 (printed page 11 onward) defines PBKDF2; Appendix B.1.2
identifies HMAC-SHA2 PRFs. RFC 4231 sections 4.2–4.8 contain HMAC test cases,
including SHA512: preserve full expected output except the explicitly truncated
case. Their independent KATs do not establish SQLCipher page compatibility.
RFC 8017 section 8.1.2 starts printed page 34 and 9.1.2 starts page 44.

| Original | SHA-256 | Official URL | Retrieved UTC |
|---|---|---|---|
| sp800-38a.pdf | 66821162de1e7130c5fb5eedb22140d8d6d013ec51af4550bb095c2a9481a00e | [sp800-38a.pdf](https://nvlpubs.nist.gov/nistpubs/Legacy/SP/nistspecialpublication800-38a.pdf) | 2026-11-03T02:20:43.2004081Z |
| rfc8018.txt | cf96b02e68216f618ea33b20b49d476edba9d70f2333597ec516629d22971cda | [rfc8018.txt](https://www.rfc-editor.org/rfc/rfc8018.txt) | 2026-11-03T02:20:43.6149090Z |
| rfc4231.txt | 72178527ce93500e730bc8eb182b857e583096d652b64ece0879c52ba1df973b | [rfc4231.txt](https://www.rfc-editor.org/rfc/rfc4231.txt) | 2026-11-03T02:20:43.9029970Z |
| rfc8017.txt | 1e72dc473d18df3fc5598cdc12795a9f18f36f1aef15abc23a55eb0d58151d11 | [rfc8017.txt](https://www.rfc-editor.org/rfc/rfc8017.txt) | 2026-11-03T02:20:44.1842181Z |
| sqlcipher-design.html | c4a161a1518322dfe757eb0d3711e2ead08efc525ff79267e0afe8535459cd0b | [sqlcipher-design.html](https://www.zetetic.net/sqlcipher/design/) | 2026-11-03T02:20:44.5122340Z |
| sqlcipher-api.html | f6caf07b6f4b90847bca3f6fd609b96873cd15e2ecab25c24c87220cabd78008 | [sqlcipher-api.html](https://www.zetetic.net/sqlcipher/sqlcipher-api/) | 2026-11-03T02:20:44.5665000Z |
| sqlcipher-v4.6.1.c | 010d418c541cd3606f58fd705ae404201fd243fd20cb387439697289a6c87219 | [sqlcipher-v4.6.1.c](https://raw.githubusercontent.com/sqlcipher/sqlcipher/c5bd336ece77922433aaf6d6fe8cf203b0c299d5/src/sqlcipher.c) | 2026-11-03T02:22:18.1144043Z |
