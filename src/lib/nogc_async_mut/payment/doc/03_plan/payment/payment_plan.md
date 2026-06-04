# Payment Submodule — Implementation Plan

## Milestones

### M1: Interface Skeleton + Types (this pass)
- [x] Research doc
- [x] MDSOC architecture doc
- [x] Gateway trait (`authorize/capture/charge/refund/void/tokenize`)
- [x] Vault trait (`store_token/retrieve/delete/list`)
- [x] Card types (`CardNumber`, `CardToken`, `PaymentIntent`, `PaymentResult`)
- [x] Card validator (Luhn, BIN detection)
- [x] CardReader trait (HW adapter interface)
- [x] Agent tool interface (token-only ops)
- [x] CLI payment skeleton
- [x] SFM manifest (Trusted)
- [x] SPipe specs — all failing (encode ACs)
- [x] TODOs for every unimplemented fn body

### M2: Mock Gateway + Memory Vault + CLI
- [ ] MockGateway impl (fake authorize/capture/refund)
- [ ] MemoryVault impl (in-memory token map)
- [ ] CLI end-to-end flow with mock data
- [ ] Agent tool wired to mock gateway
- [ ] All M1 specs passing

### M3: Real Gateway Connectors
- [ ] Stripe connector (PaymentIntent flow)
- [ ] PayPal connector
- [ ] Connector registry + routing
- [ ] Webhook handler

### M4: Encrypted Vault + KMS
- [ ] KMS-backed encryption (via `std.security.kms_provider`)
- [ ] Credential store integration
- [ ] Audit chain on all vault ops
- [ ] PCI DSS compliance checklist

### M5: HW Terminal Adapter
- [ ] EMV reader protocol
- [ ] NFC contactless
- [ ] Mag-stripe fallback
- [ ] P2PE encryption layer
- [ ] Real hardware test rig

### M6: LLM Agent Guardrails + MCP Tools
- [ ] MCP tool definitions for payment ops
- [ ] Token-only data flow enforcement
- [ ] Rate limiting + anomaly detection
- [ ] Agent payment authorization flow

## Constraints
- Pure Simple implementation (no Python/Bash)
- MDSOC+ for userland; MDSOC-only for HW driver
- SFM Trusted security level
- Never store raw PAN/CVV after tokenization
- LLM agent never sees raw card data
