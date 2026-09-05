# mcp_failure_prevention_spec pre-existing RED at HEAD (2026-08-26)

## Symptom
`bin/simple test test/03_system/app/mcp/feature/mcp_failure_prevention_spec.spl`
fails at HEAD (verified by restoring HEAD content in place, 2026-08-26):

```
Results: 5 total, 3 passed, 2 failed
```

Failing scenarios:
- `should exercise MCP and LSP protocol functions through production wrappers`
  — `interface_cache_valid=true` gate fails (marker mismatch on cache evidence)
- `should keep warm MCP and LSP startup latency request p95 and RSS bounded`
  — gate script returned `error=lsp_request_timeout:lsp-request-10` instead of
  `mcp_lsp_nfr_status=pass` (LSP request timed out at 10s)

## Handling
Left RED per testing rules; sspec-maintain modernization deferred (a scoring
fix cannot be dual-checked green on a spec whose scenarios already fail).

## Unblock condition
MCP/LSP wrapper interface-cache evidence gate and the NFR evidence script
(`scripts/check/check-mcp-lsp-nfr-evidence.shs`) must pass on this host, or
the gates need environment-appropriate timeouts.
