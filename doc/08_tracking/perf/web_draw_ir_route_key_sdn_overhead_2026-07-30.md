# Web Draw IR Route Key SDN Overhead

## Status

Measured and open. Production remains on the exact canonical SDN key.

## Evidence

`web_draw_ir_route_key_cost_spec.spl` measures three samples after three
warmups for 64, 256, and 1024 rectangle commands and asserts stable encoded
sizes and positive timings. On the source-matched incremental Rust interpreter,
median canonical SDN serialization was:

| Commands | SDN bytes | Initial median | Review median | Final median |
|---:|---:|---:|---:|---:|
| 64 | 30,571 | 345,428 us | 305,251 us | 317,359 us |
| 256 | 121,514 | 1,312,451 us | 1,207,284 us | 1,269,513 us |
| 1024 | 485,835 | 5,307,734 us | 4,820,833 us | 4,937,136 us |

The cost is outside GPU/upload timing and is paid before every policy lookup.

## Rejected Attempt

A full structural dual fingerprint preserved every serialized Draw IR field.
The first portable byte encoder timed out after 180 seconds on a two-command
unit. A reduced code-point encoder also timed out after 180 seconds. A runtime
`text_hash` variant was rejected because that symbol is not available through
the current Simple surface. Production source was restored after the
three-cycle cap.

## Required Fix

Add an exact producer-owned layout revision for the no-image HTML Draw IR
result, covering HTML, viewport, layout-affecting font/style state, and ordered
composition semantics. Cache the canonical key by that exact revision in the
existing bounded process-local route cache. Do not replace exact identity with
a probabilistic composition fingerprint.

Acceptance evidence:

- identical revision avoids SDN serialization on repeated frames;
- any HTML, viewport, font/style revision, backend, or transfer-mode change
  misses the cache;
- output parity and device provenance remain unchanged;
- paired same-host/runtime before/after runs show lower 64/256/1024 command
  median lookup time;
- CUDA live route calibration/reuse still passes; Metal repeats on the prepared
  macOS host under TODO 588.
