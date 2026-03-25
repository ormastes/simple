# Non-Functional Requirements (NFR / SLO)

Measurable quality constraints that apply across features.

NFR answers: **How well must the system work?**
These do not fit naturally into BDD feature scenarios.

---

## Categories

| Category | What it covers |
|----------|----------------|
| **Performance** | Latency, throughput, cold-start time |
| **Reliability** | Uptime, error rate, fault tolerance |
| **Security** | Crypto standards, token expiry, input validation |
| **Observability** | Logging, tracing, metrics requirements |
| **Compatibility** | Platform, OS, architecture, version targets |
| **Scalability** | Concurrent user / data volume limits |

---

## Document Template

```markdown
# NFR – [Feature / System Area]

**Related requirements:** [doc/requirement/xxx.md](../requirement/xxx.md)
**Related design:** [doc/design/xxx.md](../design/xxx.md)

## Performance

- Operation X P95 latency < Yms
- Throughput: Z requests/sec minimum

## Reliability

- Availability >= 99.X% monthly
- Error rate < 0.X%
- Graceful degradation when dependency Y is unavailable

## Security

- All tokens use HMAC-SHA256
- Tokens expire within X minutes
- No secrets in logs

## Observability

- All operations emit structured JSON logs
- Failed operations include correlation ID
- Metrics exposed at /metrics endpoint

## Compatibility

- Supports Linux x86_64, arm64
- Minimum OS version: ...
- Compiler version: ...

## Verification

How each NFR is measured / tested:
| NFR | Test / Tool | Threshold |
|-----|-------------|-----------|
| P95 latency | load test | < Xms |
| Availability | uptime monitor | >= 99.9% |
```

---

## Naming Convention

Files named: `<feature-area>.md`

Examples:
- `compiler_performance.md`
- `mcp_server_reliability.md`
- `security_baseline.md`
