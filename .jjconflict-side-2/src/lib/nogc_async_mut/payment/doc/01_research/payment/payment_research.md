# Payment/Credit Submodule — Research

## Open-Source Payment Ecosystem Survey

### 1. Hyperswitch (Juspay) — Payment Orchestrator
- **Language:** Rust | **License:** Apache-2.0
- **Architecture:** App server + card-vault + encryption-service + prism (unified connector lib)
- PCI-compliant vault for card/token/wallet/bank storage
- 100+ payment processor connectors (Stripe, Adyen, PayPal, Worldpay, etc.)
- Intelligent routing: route each transaction to highest-auth-rate PSP
- Revenue recovery: retry strategies by card BIN, region, method
- Cost observability dashboards
- **Key pattern:** Connector trait abstraction — each gateway implements a uniform interface

### 2. Active Merchant (Shopify) — Gateway Abstraction
- **Language:** Ruby | **License:** MIT | **Stars:** 4.6k
- Extracted from Shopify; canonical "payment abstraction library"
- Consistent interface: `authorize`, `capture`, `purchase`, `refund`, `void`, `store`, `unstore`
- 100+ gateway integrations
- **Key pattern:** Gateway base class with uniform response objects

### 3. Stripe API — Industry Reference Model
- Core objects: PaymentIntent, Charge, Refund, Customer, PaymentMethod
- Flow: create PaymentIntent -> confirm -> capture (or auto-capture)
- Tokenization: card data never touches merchant server
- Idempotent requests, expandable responses, webhook events
- **Key pattern:** Intent-based payment flow with explicit state machine

### 4. Square SDK — Terminal + Processing
- Payment processing + physical terminal hardware
- Terminal API: create terminal checkout, reader pairing
- **Key pattern:** Unified online + in-store payment interface

## PCI DSS Requirements (v4.0.1)

| Requirement | Impact on Design |
|---|---|
| Never store CVV/CVC after authorization | Vault stores tokens only |
| Encrypt PAN at rest (AES-256 or equiv) | KMS integration required |
| Restrict access by business need-to-know | Capability-gated SFM Trusted module |
| Log all access to cardholder data | Audit chain on every vault operation |
| Tokenize at point of entry | Card data -> token before any persistence |
| Point-to-point encryption for HW | Terminal adapter must handle P2PE |

## Design Patterns Extracted

1. **Gateway/Connector trait** — uniform `authorize/capture/charge/refund/void/tokenize`
2. **Tokenized vault** — store opaque tokens, never raw PAN; backed by KMS
3. **Intent-based flow** — PaymentIntent state machine (created->confirmed->captured->settled)
4. **Terminal abstraction** — CardReader trait for HW adapters, mock for testing
5. **Agent guardrail** — LLM operates on opaque tokens only; money movement requires explicit authz
6. **Audit chain** — every vault/payment operation logged immutably
