# rt-encapsulation — Stage 2 wrapper-gap scoping

Stage 1 (the `raw_rt_access` warn-lint + io_runtime facade fix) is landed and live.
Stage 2 = build std wrappers for `rt_*` intrinsics used by restricted code so those
modules can migrate off raw externs. This doc scopes that gap.

Privileged tiers (may declare raw `rt_*`): `src/lib`, `src/runtime`, `src/compiler`.
Restricted: `src/app`, `examples`, external. Source: lint `raw_rt_access` (RAW-RT-001).

## Gap measurement (2026-06-18)

- **767** distinct `rt_*` declared `extern` in restricted code (`src/app` + `examples`).
- **24** already covered by canonical `std.io_runtime` wrappers.
- **594** are referenced *somewhere* in `src/lib` already → a wrapper most likely
  exists; migration is mostly **mechanical** (re-point the restricted caller at the
  existing std wrapper). Low risk, high volume.
- **173 "hard gap"** — `rt_*` that `src/lib` never references at all. Breakdown:
  - **82** hardware / emulator / render (riscv, rv32/64, x86, arm32/64, mmio, pci, fb,
    gpu, gui, renderdoc, uart, qemu) — intentionally low-level.
  - **15** crypto (ed25519, sha1, tls13, ssh, x25519). `rt_ed25519_*`/`rt_ssh_*`
    already partially appear in `src/lib` crypto/net → a std.crypto/std.net home exists.
  - **13** net/protocol (net, ws, tcp/udp, dns, socket, port).
  - **63** remainder — still mostly domain-specific: `rt_layout_*` (UI), `rt_log_*`
    (logging), `rt_term_*` (terminal), `rt_test262_*` (JS suite), `rt_ipc_*`,
    `rt_mem_*`/`*_volatile_*` (baremetal), plus compiler-internal `rt_native_build`,
    `rt_compile_to_llvm_ir`, `rt_new_function`.

Distribution of the hardware+crypto hard-gap externs: **5 files in `src/app`, 40 files
in `examples/`** — the bulk is example demos, not first-party app code.

## The genuinely-general subset (the real, bounded Stage-2 wrapper work)

These 8 are general-purpose I/O/sys with **no** existing lib wrapper — build them in
`std.io_runtime` (or a small `std.log` / `std.term`):

| rt_* | proposed wrapper home |
|------|------------------------|
| `rt_file_list_dir` | `std.io_runtime.list_dir` (variant of existing `dir_list`) |
| `rt_get_cwd` | `std.io_runtime.cwd` (currently shells out; add direct) |
| `rt_stdin_read_bytes` | `std.io_runtime` stdin reader |
| `rt_shell_exit_code` | `std.io_runtime` (shell result already exposes code) |
| `rt_process_get_rss_kb` | `std.io_runtime` process introspection |
| `rt_random_bytes_c` | `std.common.crypto` or `std.io_runtime` random |
| `rt_term_write` / `rt_term_*` | `std.term` (terminal I/O) |
| `rt_log_emit` / `rt_log_*` | `std.log` (structured logging) |

## Open design decision (blocks the bulk migration, NOT the 8 wrappers above)

The user's Stage-0 boundary choice was "stdlib + runtime only, migrate everything."
The scope shows ~110 hardware/crypto/protocol intrinsics across **40 example demos**
that are intentionally low-level (emulators implementing CPUs, baremetal MMIO, GPU
probes, crypto impls). Forcing those through std wrappers is high-effort / low-value
and sometimes semantically wrong. Options:

- **A. Exempt `examples/**`** from `raw_rt_access` (demos, often deliberately low-level);
  focus migration on the 5 `src/app` hardware files + the general I/O subset.
- **B. Build domain std modules** (`std.gpu`, `std.crypto`, `std.net.tls`) and migrate
  examples to them. Highest effort; some modules partially exist.
- **C. `@runtime_intrinsics` opt-in attribute** for legitimately low-level modules
  (the opt-in boundary option not originally chosen) — path-independent exemption.

Recommendation: **A + build the 8 general wrappers now**, defer B/C per domain.

**DECISION (2026-06-18): Option C chosen + build the 8 wrappers now.** The
`@runtime_intrinsics` / `#[runtime_intrinsics]` file-level opt-out marker is
implemented and live in both the Rust seed and pure-Simple `raw_rt_access` lint
(whitelisted as a known decorator/attribute; verified: marked file → 0 findings,
unmarked → warns). Low-level modules (emulators, baremetal, crypto/protocol
impls) declare the marker to keep raw `rt_*`; everything else still migrates.

## Suggested Stage-2 order

1. Build the 8 general-purpose wrappers (bounded, no design dependency).
2. Decide examples/ treatment (A/B/C above).
3. Mechanical migration of the 594 soft-gap callers to existing std wrappers
   (scriptable; one domain at a time).
4. Then Stage 3 (migrate remaining restricted files) → Stage 4 (flip lint to deny).

Related: lint `raw_rt_access`, `doc/07_guide/app/lint.md`, memory
`project_rt_encapsulation_rollout`.

## CORRECTION (2026-06-18): the general-gap rt_* are largely UNIMPLEMENTED

Attempting Stage 2a (build the 8 general wrappers) showed the premise was wrong.
Of the 8 "genuinely-general" rt_*, only `rt_get_cwd` actually runs in the
interpreter. Verified: `rt_file_list_dir` **core-dumps** when called;
`rt_stdin_read_bytes`, `rt_shell_exit_code`, `rt_process_get_rss_kb`,
`rt_random_bytes_c`, `rt_term_write`, `rt_term_flush` are registered **NOWHERE**
in the standard backends (interpreter `interpreter_extern/` + native
`runtime_sffi.rs`); `rt_term_poll`/`rt_term_read_timeout` exist only in a
pure-Simple runtime core (`src/runtime/simple_core/core_process.spl`).

So the restricted apps/examples that declare these are native-special or stale —
the gap is **not "missing wrappers" but "missing/broken intrinsics."** The wrapper
batch was **reverted** from `io_runtime.spl` to avoid shipping core-dumping std
APIs (extern decls are lazy, but a std-blessed `random_bytes()` that cores when
called is a footgun).

**Revised Stage-2 method:** before wrapping any rt_*, verify it is implemented and
callable in the target backend (run a smoke call, not just a name grep). The real
Stage-2 work is (a) the `@runtime_intrinsics` opt-out (DONE) for legitimately
low-level modules, and (b) the **mechanical migration of the 594 soft-gap callers**
to *existing, working* std wrappers — not building new wrappers for unimplemented
intrinsics.
