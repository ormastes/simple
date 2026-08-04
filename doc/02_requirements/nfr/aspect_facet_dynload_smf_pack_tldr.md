# Aspect Facet NFRs — TL;DR

```sdn
nfr:
  deterministic: catalogs + cache_keys
  cold: zero_pack_io
  bounded: decode + cache + subprocess_capture
  secure: signed_fail_closed
```

- Patchable advice never claims exact zero overhead.
- Cache keys bind pack/module digest, target, variant fingerprint, and ABI.
- Cold manual/lazy facets do no pack I/O, decoding, mapping, allocation, or scanning.
- Baselines drive startup/first-use/lookup thresholds.
- Mission-critical defaults deny lazy operational I/O and dynamic mutation.
- SFM evolves; ordinary SMF remains compatible.

