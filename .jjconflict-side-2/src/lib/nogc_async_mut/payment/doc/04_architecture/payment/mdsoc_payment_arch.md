# MDSOC+ Payment Architecture

## Capsule Decomposition

```
simple-payment/
  src/
    gateway/         # MDSOC+ (ECS business) — connector abstraction
    vault/           # MDSOC+ (ECS business) — tokenized card storage
    card/            # MDSOC+ (ECS business) — card types + validation
    agent/           # MDSOC+ (ECS business) — LLM/CLI payment surface
    sfm/             # MDSOC  (outer only)   — SFM manifest + packaging
    hw/              # MDSOC  (driver only)  — HW terminal adapter
```

### MDSOC+ Layer Split

| Layer | Concern | MDSOC Role |
|---|---|---|
| Gateway trait | Connector interface | Dimension (cross-cutting) |
| Connector impls | Stripe/PayPal/mock | Feature capsule |
| Vault trait | Token storage interface | Dimension |
| Vault impls | Memory/encrypted vault | Feature capsule |
| Card types | PAN, expiry, token types | Data dimension |
| Card validator | Luhn, BIN lookup | Pure function dimension |
| CardReader trait | HW adapter interface | Driver dimension (MDSOC-only) |
| Agent tool | LLM-facing payment ops | Front-end capsule |
| CLI | Terminal payment access | Front-end capsule |
| SFM manifest | Module boundary + authz | Capsule boundary |

### Security Boundary (SFM Trusted)

```
                LLM Agent / CLI
                    |
            [opaque tokens only]
                    |
            SFM Authz Gate (Trusted)
                    |
        +-----------+-----------+
        |                       |
   Gateway Layer           Vault Layer
   (connector calls)    (token store + KMS)
        |                       |
   External PSP           Encrypted Storage
   (Stripe, etc.)       (credential_store + kms_provider)
```

- LLM/CLI never sees raw card data — only opaque payment tokens
- Money movement (authorize/capture/charge) requires explicit `PaymentAuthz` capability
- Vault operations audit-logged via `std.security.audit_chain`
- SFM security level: `Trusted` — authz gate enforced on all entry points

### Dependency Map (stdlib)

| This module uses | stdlib path |
|---|---|
| SFM packaging | `std.sfm` (codec, manifest, di_bridge, authz, loader) |
| Secure credential store | `std.security.auth.credential_store` |
| KMS encryption | `std.security.kms_provider` |
| Capability enforcement | `std.security.enforcement.capability` |
| Audit logging | `std.security.audit_chain` |
| HTTP client (gateway calls) | `std.http` |
| Async I/O | `std.async` (nogc_async_mut tier) |

### HW Terminal Adapter (MDSOC-only, future milestone)

- `CardReader` trait: `read_card() -> CardToken`, `check_status() -> ReaderStatus`
- Mock impl for testing; real EMV/NFC/mag-stripe adapters are cert-bound
- P2PE (point-to-point encryption) required for PCI compliance
- This layer stays MDSOC-only (no ECS); it is a driver, not userland business logic
