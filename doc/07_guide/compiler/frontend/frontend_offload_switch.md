# Frontend Offload Switch (GPU frontend on/off)

The compiler frontend (lex/structure + parse stages) can be asked to leave the
CPU. The switch is **off by default**; nothing changes for the Rust seed,
bootstrap, or CPU-only hosts. Turning it on never silently succeeds: while the
GPU parse path is unimplemented the compiler records a demotion receipt, and
under `require-requested` it fails the compile.

## Keys

| Source | Key | Values |
|---|---|---|
| CLI | `--frontend-offload=<v>` | `off` · `on` (alias `hybrid`) · `resident` · `auto` |
| env | `SIMPLE_FRONTEND_OFFLOAD=<v>` | same |
| `simple.sdn` | `frontend: { offload: <v> }` | same — not read yet (Wave 1, GFO-005); the resolver slot is tested with injected text |
| CLI | `--frontend-offload-fallback=<p>` | `allow-cpu` (default) · `require-requested` |
| env | `SIMPLE_FRONTEND_OFFLOAD_FALLBACK=<p>` | same |
| `simple.sdn` | `frontend: { offload_fallback: <p> }` | same — not read yet (Wave 1, GFO-005) |

Precedence: CLI > env > config > default (`off`, `allow-cpu`). The CLI flag only
sets the env var, so the driver has one read path. An unknown value is an error.

## What each value means today (Wave 0)

| Requested | `allow-cpu` | `require-requested` |
|---|---|---|
| `off` | CPU oracle, reason `""` | same |
| `on` / `resident` | CPU oracle, reason `parse_mode_unimplemented` | compile fails: `frontend_offload_required_mode_unavailable: <mode>` |
| `auto` | CPU oracle, reason `auto_profile_not_implemented_wave_1` (no retained crossover evidence yet) | compile fails: `frontend_offload_required_mode_unavailable: auto` |

`off` and `on` + `allow-cpu` produce the same `deterministic_hash`; that parity
is the invariant later GPU waves must keep.

## Receipt

With `SIMPLE_INTERP_TRACE=1` the driver prints one line:

```text
[frontend-offload] requested=hybrid_vector_gpu selected=cpu_reference reason=parse_mode_unimplemented source=env
```

Native-build warm caching folds the same decision into its identity digest as
`frontend_offload_requested=`, `frontend_offload_selected=`,
`frontend_offload_reason=`, `frontend_offload_source=` rows (or one
`frontend_offload_error=` row), derived by the shared `frontend_offload_rows`
helper so it cannot drift from the driver's receipt. A switch change therefore
never reuses a warm artifact built under another decision; adding the rows
invalidated every pre-existing warm identity once.

## Where it lives

- Pure resolver: `src/compiler/00.common/structural_contracts/frontend_offload_switch.spl`
  (`resolve_frontend_offload`, `frontend_offload_profile`, `frontend_offload_decision`).
- Driver read + receipt: `src/compiler/80.driver/driver_source_pipeline_parsing.spl`
  (`driver_frontend_offload_switch`, `driver_frontend_offload_decision`).
- Design: `doc/05_design/compiler/frontend/gpu_frontend_offload_switch_design.md`;
  staged GPU/SIMD waves: `doc/03_plan/compiler/frontend/gpu_frontend_offload_plan.md`.

## Troubleshooting

- Receipt says `source=env` although you passed the CLI flag: the CLI layer
  writes the env var, so `env` is the expected source for a CLI request.
- The deployed `bin/simple` is the Rust seed: it does not run the pure-Simple
  driver, so the switch is only observable on a self-hosted binary. Check with
  `readlink -f bin/simple && bin/simple --version`.
