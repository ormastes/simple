# simple-payment

Credit and payment access interface library for Simple Language.

MDSOC+ architecture. SFM Trusted module. Pure Simple implementation.

## Features

- **Gateway abstraction** — `authorize/capture/charge/refund/void/tokenize` across payment processors
- **Tokenized vault** — PCI-aware card storage (never stores raw PAN/CVV)
- **Card validation** — Luhn check, BIN detection, expiry validation
- **HW terminal adapter** — CardReader trait for EMV/NFC/mag-stripe readers
- **LLM agent tool** — token-only payment interface (agent never sees raw card data)
- **CLI payment** — terminal-based payment operations

## Status

**M1: Interface skeleton** — traits, types, failing specs, TODOs.

## Usage

```bash
# Run tests (all currently failing — skeleton only)
bin/simple test test/gateway_spec.spl
bin/simple test test/vault_spec.spl
bin/simple test test/card_spec.spl
bin/simple test test/agent_spec.spl
bin/simple test test/sfm_spec.spl
```

## Architecture

See `doc/04_architecture/payment/mdsoc_payment_arch.md`.

## License

Apache-2.0
