# Encoding & Codec — Agent Task Plan (2026-05-03)

## Status Summary

| Module | Standard | Status | Tests |
|--------|----------|--------|-------|
| Base64 | RFC 4648 | Done | pass |
| Base32/32hex | RFC 4648 | Done | pass |
| Base58/58check | Bitcoin | Done | pass |
| PEM | RFC 7468 | Done | pass |
| ASN.1 DER | X.690 | Done | pass |
| YAML | YAML 1.2 | Done | 27 pass |
| TOML | TOML v1.0 | Done | pass |
| INI | .ini format | Done | pass |
| JSON | RFC 8259 | Done | pass |
| BSON | MongoDB spec | Done | pass |
| UTF-8/16/32 | Unicode | Done | pass |
| BIP32 | HD wallet | Done | pass |
| HOTP-SHA256/512 | RFC 4226 ext | Done | pass |
| `bencode.spl` | BitTorrent | File exists | needs spec |
| `msgpack.spl` | MessagePack | File exists | needs spec |
| `protobuf.spl` | Protobuf wire | File exists | needs spec |
| `cose.spl` | RFC 9052 | File exists | needs spec |
| CBOR | RFC 8949 | Not started | — |

## Implemented (14 modules)

All in `src/lib/common/encoding/` unless noted.

### Binary Formats (complete)
- `base58.spl` — Base58 + Base58check (Bitcoin address encoding)
- `bson.spl` — BSON encoder/decoder (MongoDB wire format)
- ASN.1 DER — X.690 Distinguished Encoding Rules

### Text Formats (complete)
- `yaml.spl` — YAML 1.2 parser (27 tests)
- `toml.spl` — TOML v1.0
- `ini.spl` — INI file parser
- JSON — RFC 8259 (in std.json)

### Character Encodings (complete)
- `utf8.spl`, `utf16.spl`, `utf32.spl` — Full Unicode support

### Crypto-Adjacent Encodings (complete, in `src/os/crypto/`)
- `pem.spl` — PEM RFC 7468 encoder/decoder
- BIP32 — HD wallet key derivation
- HOTP-SHA256/SHA512 — RFC 4226 extended

---

## Remaining Work

### Priority 1 — Verify Existing Files (need KAT specs)
| Module | File | Agent Scope |
|--------|------|-------------|
| Bencode | `src/lib/common/encoding/bencode.spl` | Write spec, verify round-trip |
| MessagePack | `src/lib/common/encoding/msgpack.spl` | Write spec, verify round-trip |
| Protobuf | `src/lib/common/encoding/protobuf.spl` | Write spec, verify encode/decode |
| COSE | `src/os/crypto/cose.spl` | Write Sign1+Mac0 spec |

### Priority 2 — New Implementations
| Module | Standard | Notes |
|--------|----------|-------|
| CBOR | RFC 8949 | Core binary format, needed by COSE |
| BIP39 | BIP-0039 | Mnemonic seed phrases (blocked by content-filter) |

---

## Agent Spawn Guide

```
Agent scope: src/lib/common/encoding/<module>.spl (or src/os/crypto/ for crypto-adjacent)
Test scope:  test/unit/lib/common/encoding/<module>_spec.spl
Verify:      bin/simple test test/unit/lib/common/encoding/<spec>.spl
Pattern:     encode(data) -> [u8], decode(bytes) -> Result<T, Error>
```
