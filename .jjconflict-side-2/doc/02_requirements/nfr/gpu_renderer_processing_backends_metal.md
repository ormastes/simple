# Metal MSL Processing Backend NFRs

- NFR-001: Equal validated IR and generator version produce byte-identical MSL
  and identical semantic cache keys.
- NFR-002: Generation performs no device probing, filesystem scan, or subprocess
  launch and is linear in emitted source size.
- NFR-003: The first native compile may populate an artifact cache; a cache hit
  must avoid source recompilation.  Any IR semantic, ABI, entry-point, or
  generator-version change invalidates the entry.
- NFR-004: Host-independent generation target is below 10 ms and 8 MiB peak RSS
  for representative renderer kernels.  Native cold compile and dispatch are
  recorded separately; no unavailable-host timing is reported as PASS.
