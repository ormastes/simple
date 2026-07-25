# Payment Submodule — Implementation Plan

## Milestones

### M1: Interface Skeleton + Types [DONE]
- [x] Research doc
- [x] MDSOC architecture doc
- [x] Gateway trait, Vault trait, Card types, CardReader trait
- [x] Agent tool interface + CLI skeleton + SFM manifest (Trusted)
- [x] SPipe specs — 60 failing tests encoding ACs
- [x] TODOs for every unimplemented fn body

### M2: Working Payment Core [CURRENT]
- [ ] **Card validator impl** — Luhn algorithm, BIN-based brand detection, expiry check, masking
- [ ] **MockGateway impl** — fake authorize/capture/charge/refund/void with transaction ID generation, idempotency map, fail-mode toggle
- [ ] **MemoryVault impl** — in-memory token map, store/retrieve/delete/list, token generation from card data (last4 + brand extraction), never persist raw PAN
- [ ] **ConnectorRegistry impl** — register connectors with priority, route by priority/currency
- [ ] **CLI end-to-end** — `add-card` (prompt → tokenize → vault store), `list-cards` (masked display), `charge` (token → gateway), `refund`, `status`
- [ ] **Agent tool validation** — reject raw PAN/CVV in token field, accept only `tok_*` prefixed tokens
- [ ] All 60 M1 specs passing green

### M3: Real Gateway Connectors
- [ ] **Stripe connector** — PaymentIntent flow (create → confirm → capture), API key config, webhook signature verification
- [ ] **PayPal connector** — Orders API v2 (create → capture), OAuth2 token exchange
- [ ] **Connector registry routing** — route by currency/region/amount/success-rate; fallback on PSP downtime
- [ ] **Webhook handler** — generic webhook dispatcher, per-connector signature verification, idempotent event processing
- [ ] **HTTP retry + circuit breaker** — exponential backoff, per-connector circuit state, timeout config
- [ ] New specs: `stripe_spec.spl`, `paypal_spec.spl`, `webhook_spec.spl`, `routing_spec.spl`

### M4: Encrypted Vault + Audit
- [ ] **KMS-backed encryption** — encrypt token store at rest via `std.security.kms_provider`, key rotation support
- [ ] **Credential store integration** — API keys/secrets stored in `std.security.auth.credential_store`, never in config files
- [ ] **Audit chain** — immutable log of every vault/payment operation via `std.security.audit_chain`
- [ ] **PCI DSS self-assessment** — requirement checklist mapped to implementation (SAQ-A scope for tokenized flow)
- [ ] New specs: `kms_vault_spec.spl`, `audit_spec.spl`

### M5: HW Terminal Adapter
- [ ] **EMV chip reader** — ISO 7816 APDU command sequences, application selection, PIN verification flow
- [ ] **NFC contactless** — ISO 14443 tap-to-pay, PPSE selection, contactless transaction limits
- [ ] **Mag-stripe fallback** — track 1/2 parsing, PAN extraction, CVV-from-track derivation
- [ ] **P2PE encryption** — point-to-point encryption layer, HSM key injection, SRED compliance markers
- [ ] **Mock HW test harness** — simulated card read sequences for CI
- [ ] New specs: `emv_reader_spec.spl`, `nfc_spec.spl`, `magstripe_spec.spl`

### M6: LLM Agent + MCP Tools
- [ ] **MCP tool definitions** — `payment.charge`, `payment.refund`, `payment.list-methods`, `payment.add-card` as MCP tool schema
- [ ] **Token-only enforcement** — AOP aspect rejecting any request containing PAN-shaped data (13-19 digit sequences)
- [ ] **Rate limiting** — per-agent, per-method rate limits; anomaly detection (unusual amount patterns)
- [ ] **Authorization flow** — human-in-the-loop confirmation for charges above threshold; agent can only pre-stage, human confirms
- [ ] **Agent payment history** — read-only transaction log access (masked amounts, no card data)
- [ ] New specs: `mcp_tool_spec.spl`, `agent_rate_limit_spec.spl`, `agent_authz_spec.spl`

### M7: Web Store App Integration
- [ ] **Store checkout flow** — cart → payment-intent → confirm → capture → receipt
- [ ] **Saved payment methods** — customer vault with multiple cards, default selection
- [ ] **Subscription/recurring billing** — create subscription, retry on failure, dunning management
- [ ] **Refund/dispute handling** — customer-initiated refunds, chargeback webhook processing
- [ ] **Store admin dashboard** — transaction list, refund actions, settlement reports
- [ ] New specs: `checkout_spec.spl`, `subscription_spec.spl`, `store_admin_spec.spl`

## Constraints
- Pure Simple implementation (no Python/Bash)
- MDSOC+ for userland; MDSOC-only for HW driver
- SFM Trusted security level
- Never store raw PAN/CVV after tokenization
- LLM agent never sees raw card data
- Real HTTP calls to Stripe/PayPal APIs (M3+)
- Encrypted storage at rest for all secrets (M4+)
- Human-in-the-loop for agent-initiated charges above configurable threshold
