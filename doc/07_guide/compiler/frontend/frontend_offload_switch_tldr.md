# Frontend Offload Switch — TL;DR

- Default **off**. `--frontend-offload=off|on|resident|auto`,
  `SIMPLE_FRONTEND_OFFLOAD`, `simple.sdn frontend.offload` (reader is Wave 1, GFO-005); CLI > env > config.
- Fallback `allow-cpu` (default) or `require-requested` via
  `--frontend-offload-fallback` / `SIMPLE_FRONTEND_OFFLOAD_FALLBACK` / `frontend.offload_fallback`.
- Wave 0: GPU parse unimplemented → `on` demotes with reason
  `parse_mode_unimplemented`, `auto` with `auto_profile_not_implemented_wave_1`;
  `require-requested` fails the compile.
- Receipt (`SIMPLE_INTERP_TRACE=1`): `[frontend-offload] requested= selected= reason= source=`.
- Only observable on a self-hosted binary; the Rust seed ignores it.

<!-- sdn-diagram:frontend-offload-switch-tldr -->
```sdn
{cli, env, simple.sdn (Wave 1 GFO-005), default off} -> resolve_frontend_offload -> frontend_offload_decision -> {receipt, parse mode}
```
