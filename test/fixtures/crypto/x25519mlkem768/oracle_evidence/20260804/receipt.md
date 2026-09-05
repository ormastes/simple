# X25519MLKEM768 free/open oracle receipt — 2026-08-04

- ML-KEM fixture SHA-256: `ae9f144c2ed655990eac4257df9851c5ca3cae9e30feb65ae5d0980d151af207`
- Hybrid fixture SHA-256: `156dbf854aabea142c67df4a4af2c1f131fef66bb8da2f4ec2b16168726da858`
- Go comparator: exit `0`; raw-log SHA-256 `66a69d66d97c373f76f925bfdad6126289e767a2120e671e41827e6341f27bb4`
- CIRCL comparator: exit `0`; raw-log SHA-256 `9b91e98e17f976b95ec3651a614cd7f6549f10ecafde132038297f9ef569e073`
- Both logs contain exactly one structured Set A, Set B, and Set C record,
  derived from the compared outputs and including their exact lengths and
  SHA-256 values.
- Execution used the pinned Go 1.24 toolchain with `GOTOOLCHAIN=local`,
  `GOPROXY=off`, and `GOSUMDB=off`; no network access or GOROOT mutation was
  permitted.

Status: PASS for the Go and CIRCL free/open comparators. Pure-Simple native
Set A/B/C execution remains unverified and is not promoted by this receipt.
