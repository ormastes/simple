# HTTP server `parse_config_text` misses block SDN server config

Date: 2026-06-16
Severity: P2
Status: open

## Summary

While adding reverse proxy active health-check config coverage,
`parse_config_text` returned `ConfigError("Missing 'server' block")` for a
block-style SDN fixture shaped like the documented HTTP server config:

```sdn
server:
    upstreams:
        - name: "backend"
          health_check_interval: 2500
          health_check_max_probes: 2
          servers:
              - addr: "127.0.0.1:3000"
                weight: 1
```

The reverse proxy active health-check fields were still added to
`UpstreamConfig` and `parse_upstream`, but runtime parser coverage was not kept
in the proxy spec because the broader SDN block parsing path needs repair first.

## Reproduction

Run a small Simple program in the repo that calls
`std.http_server.config.parse_config_text` with the fixture above and prints
`std.http_server.error.error_message` for the `Err` case.

Expected: one upstream with `health_check_interval_ms == 2500` and
`health_check_max_probes == 2`.

Actual: `Missing 'server' block`.
