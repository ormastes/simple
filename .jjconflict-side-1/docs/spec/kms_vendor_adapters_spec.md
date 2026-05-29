# Kms Vendor Adapters Specification

## At a Glance

| Field | Value |
|-------|-------|
| Source | `test/unit/lib/security/kms_vendor_adapters_spec.spl` |
| Updated | 2026-05-23 |
| Generator | `simple spipe-docgen` (Rust) |

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |

## Overview

Documentation was generated from executable SPipe scenarios.

## Evidence

| Category | Count |
|----------|------:|
| Artifacts | 2 |
| Logs | 5 |

### Artifacts

| Item | Kind | Path |
|------|------|------|
| `result.json` | JSON artifact | `build/test-artifacts/unit/lib/security/kms_vendor_adapters/result.json` |
| `summary.txt` | Text artifact | `build/test-artifacts/unit/lib/security/kms_vendor_adapters/summary.txt` |

### Logs

| Item | Kind | Path |
|------|------|------|
| `combined.log` | Log file | `build/test-artifacts/unit/lib/security/kms_vendor_adapters/combined.log` |
| `output.log` | Log file | `build/test-artifacts/unit/lib/security/kms_vendor_adapters/output.log` |
| `run.log` | Log file | `build/test-artifacts/unit/lib/security/kms_vendor_adapters/run.log` |
| `stderr.log` | Log file | `build/test-artifacts/unit/lib/security/kms_vendor_adapters/stderr.log` |
| `stdout.log` | Log file | `build/test-artifacts/unit/lib/security/kms_vendor_adapters/stdout.log` |

## Scenarios

- builds AWS KMS Sign and Verify JSON RPC requests
- builds Google Cloud KMS asymmetricSign requests
- builds Azure Key Vault sign and verify requests
- builds PKCS11 HSM gateway requests
- does not include raw signing key fields
