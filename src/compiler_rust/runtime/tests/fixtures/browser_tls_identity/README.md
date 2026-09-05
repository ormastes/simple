# Browser TLS identity fixtures

Test-only P-256 identities for `net_http_job.rs`. The CA directly signs two
server certificates: `localhost.pem` has only `DNS:localhost`, while
`wrong-host.pem` has only `DNS:wrong-host.test`. All certificates use fixed
serials and the validity window `2020-01-01T00:00:00Z` through
`2049-12-31T23:59:59Z`.

Generated with OpenSSL 3.0.13 using EC P-256 keys, SHA-256 signatures, critical
CA/key-usage constraints, and serverAuth EKU on both leaves. The source keys and
certificates are intentionally test-only and must never be installed or used by
production trust configuration.

SHA-256 certificate fingerprints:

- CA: `D3:03:9B:98:22:34:3D:79:EE:B4:BD:3D:56:26:D0:C5:2E:62:5F:1A:8C:4A:22:EF:DC:29:33:E4:FB:EC:2E:25`
- localhost: `80:1D:2B:F3:E3:97:D4:13:32:3A:0B:E7:E4:D0:02:F0:7E:C2:8B:92:1C:14:AB:29:36:7B:1F:0D:3F:83:2B:96`
- wrong host: `FB:2B:94:D3:DD:C5:97:EA:1A:28:B0:89:87:1D:B3:5D:6F:6D:63:05:90:00:7C:F4:8A:BC:0B:88:B9:20:45:11`
