# SOSIX host io layer: thin Windows backend + io spec host-gating (2026-11-12)

- **Status:** LANDED AS PR (work/fix-sosix-io-20261112) — POSIX oracles unchanged
- **Lane:** phase-2 io lane, SOSIX-IO agent
- **Companion tracking doc:** `phase2_io_lane_posix_on_windows_skip_classes_2026-11-12.md`

## Product change (thin, pass-through only)

`src/lib/nogc_async_mut/sosix/host_facade.spl`:

1. `sosix_dir_list_checked` no longer requires the POSIX text provider on
   Windows. It delegates directory enumeration to the existing
   cross-platform `dir_list_optional` (readdir on POSIX; FindFirstFile/read_dir
   on Windows) and keeps the unchanged strict UTF-8 admission loop per entry.
   No new buffers, no per-call allocation beyond the callee's own, no new
   abstraction layer.
2. `sosix_spawn_checked` gains the same Windows branch shape that
   `sosix_run_bounded_checked` already had: skip the POSIX provider
   requirement, treat `\`/`:` as explicit-path separators, resolve bare names
   through `sosix_which_checked` (the existing `process_windows_executable`
   PATH/PE lookup), then delegate to the existing `process_spawn_async` seam.
   POSIX behavior is byte-identical (the provider check is only skipped when
   `platform_name() == "windows"`).

The facade module docstring is updated to match (directory listing and spawn
now admit Windows; ordinary console text remains POSIX-only).

## sosix_tool_text_spec.spl — 0/11 fail -> 6 pass / 5 skip (exit 0)

All examples now route through the SOSIX host facade; raw `/bin/sh` and
`/tmp` usages were replaced with facade resolution and `get_temp_dir()`.
Scratch and resolution behavior on POSIX is unchanged (`/bin/sh` resolves
through `which` exactly as before).

| Example | Before (Windows) | After (Windows) | Disposition |
|---|---|---|---|
| preserves missing, empty, Unicode and malformed environment distinctions | fail (`rt_env_set: value must be a string` from `bytes_to_text([255u8])`) | PASS | portable distinctions run everywhere; only the invalid-UTF-8 env injection is branched behind `not is_windows()` — the Windows seed runtime cannot materialize malformed UTF-8 text, so the Codec oracle stays qualified on POSIX |
| returns normalized current directory and nonASCII directory names | fail (`Unsupported: ... unavailable: windows` from `sosix_dir_list_checked`) | PASS | fixed by the thin Windows dir_list backend (unicode entry names round-trip) |
| normalizes bare resolution before returning a path and then executes it | fail (resolved path has no `/`) | PASS | separator oracle is host-honest: explicit path must contain `/` (POSIX) or `\` (Windows); bare `sh` resolves and executes through the facade on both hosts |
| returns checked malformed output errors and explicit legacy process failure | fail (raw `/bin/sh` on Windows) | PASS | bare `sh` through facade capture; malformed-output decode error, legacy `-1` + "external text" message, NUL-argument admission, bad-argument spawn admission are all host-independent |
| preserves NUL in length-delimited child capture and validates bounded options | fail (raw `/bin/sh`) | PASS | bounded bytes path preserves NUL on both hosts; option validation is pure admission |
| captures exact ordinary SOSIX stdout and stderr from the native fixture | fail (missing fixture env) | SKIP | native fixture binary is built only by the admitted POSIX compiler campaign; POSIX behavior unchanged (missing fixture = FAILURE there) |
| observes explicit legacy failure for malformed environment through a native child | fail (missing fixture) | SKIP | same fixture gate |
| executes bounded repeated conversion and oversized-admission oracles | fail (missing fixture) | SKIP | same fixture gate |
| rejects a real undecodable directory entry inside SOSIX | fail (missing fixture) | SKIP | same fixture gate |
| rejects malformed resolver output before trimming or path interpretation | fail (missing fixture) | SKIP | same fixture gate |
| retains real provider timeout and capture-truncation diagnostics | fail (raw `/bin/sh`; also wrong marker for interpreter path) | PASS | timeout receipt now accepts exactly the two documented provider markers: `"[TIMEOUT: ...]"` (C runtime) and `"Process timed out"` (interpreter extern); truncation oracle unchanged |

## sosix_stdin_session_spec.spl — 0/17 fail -> 1 pass / 17 skip (exit 0)

| Example | Before (Windows) | After (Windows) | Disposition |
|---|---|---|---|
| (new) admits stdin session metadata and reports the host provider capability honestly | n/a | PASS | pins the pure codec metadata oracles the fixture modes rely on (invalid limits, unknown encoding, byte-order-less UTF-16 rejected before IO) and asserts the honest capability: `sosix_stdin_utf8` is admitted on POSIX, reports `Err(Unsupported)` on Windows. Keeps the spec non-vacuous when every pipe example is host-skipped. |
| all 17 pipe examples | fail (unwrap on missing `SIMPLE_STDIN_SESSION_FIXTURE`) | SKIP (17) | the fixture is a native POSIX binary (built only by the admitted POSIX compiler campaign) and the examples pipe bytes through `/bin/sh printf` pipelines with raw fd0 observations (`exec 0<&-`, borrowed fd0 reads) that have no honest Windows provider. POSIX behavior unchanged: fixture required, missing = FAILURE. |

## external_file_io_spec.spl — 9/11 -> 9 pass / 2 skip (exit 0)

| Example | Before (Windows) | After (Windows) | Disposition |
|---|---|---|---|
| keeps legacy positional writes write-only and does not widen creation mode | fail (`expected 420 to equal 128`) | SKIP | POSIX mode bits: `set_permissions` (package_sffi) is documented Unix-only and `rt_file_mode` reports the CRT approximation (0644) on Windows. POSIX-mode ACL emulation was rejected as not genuinely cheap. Oracle unchanged; qualified on POSIX. |
| keeps empty legacy appends successful without creating files or parents | fail (`file_append` creates the absent file) | SKIP | Windows CRT append opens the absent path before the empty write; the POSIX no-create empty-append contract has no honest Windows provider. Oracle unchanged; qualified on POSIX. |
| other 9 examples | pass | PASS | unchanged |

## external_text_io_spec.spl — 3/4 -> 3 pass / 1 skip (exit 0)

| Example | Before (Windows) | After (Windows) | Disposition |
|---|---|---|---|
| rejects unchecked malformed internal text on output and legacy input | fail (seed semantic error: `type mismatch: cannot convert str to int`) | SKIP | the example must materialize malformed UTF-8 as `text`; the Windows seed runtime cannot represent it. Oracle unchanged; qualified on POSIX. |
| other 3 examples | pass | PASS | unchanged |

## file_handle_nullable_read_spec.spl — 3/4 -> 3 pass / 1 skip (exit 0)

| Example | Before (Windows) | After (Windows) | Disposition |
|---|---|---|---|
| keeps native read failures distinct from EOF through all text and byte facades | fail (read on write-only descriptor succeeds/EOF) | SKIP | the Windows file provider collapses a read on a write-only descriptor to EOF instead of a typed access error (EBADF). The failure-vs-EOF distinction stays qualified on POSIX. Oracle unchanged. |
| other 3 examples | pass | PASS | unchanged |

## file_text_session_spec.spl — 19/21 -> 19 pass / 2 skip (exit 0)

| Example | Before (Windows) | After (Windows) | Disposition |
|---|---|---|---|
| validates convenience output before truncation and preserves legacy empty append | fail (seed semantic error from `bytes_to_text([192,128])`) | SKIP | malformed-text materialization is impossible on the Windows seed, and the empty-append half asserts the POSIX no-create append contract the Windows CRT provider does not provide. Oracle unchanged; qualified on POSIX. |
| closes owning write failures and positioned read failures on real descriptors | fail (access-mode violations succeed) | SKIP | the Windows file provider does not enforce descriptor access modes (write to read-only / positioned read on write-only succeed instead of typed access errors). Oracle unchanged; qualified on POSIX. |
| other 19 examples | pass | PASS | unchanged |

## sosix consumer specs updated to the honest Windows contract

Both pinned the old "Windows must refuse" contract that this lane deliberately
changes; both now pass on Windows with the contract asserted for every host.

- `test/01_unit/app/mcp/api_tools_sosix_boundary_spec.spl` — "pins the platform
  contract for native directory listings": on Windows `sosix_dir_list_checked`
  now lists the real entries (3/3 pass).
- `test/03_system/acceptance/sosix_host_process_services_acceptance_spec.spl` —
  "observes and terminates a live child on this host": renamed from
  "...on POSIX hosts"; Windows now spawns the resolved `sh`, observes
  liveness, kills, and confirms termination (4/4 pass). The remaining
  `else` branch (hosts with no spawn provider, e.g. SimpleOS) still asserts
  the explicit `Unsupported` error.

## Verification (all on Windows, worktree `fix-sosix-io-wt`, seed `bin/simple.exe`, `--mode=interpreter`)

- 6 io specs: all `outcome=OK`, exit 0 (counts above).
- 2 consumer specs: `outcome=OK`, exit 0.
- `test/02_integration/app/mcp_stdio_integration_spec.spl` (required src/lib
  gate): 12/16 fail with "MCP executable and input paths must be nonempty" —
  PRE-EXISTING host precondition (the spec needs a built MCP server binary;
  it imports no sosix surface and touches none of these changes). Not a
  regression; recorded here for the qualification lane.
- Untracked probe specs used during development lived under
  `build/sosix-io-agent/` (git-ignored) and were deleted.

## Follow-ups for other lanes (not this lane's scope)

- Windows seed runtime cannot materialize malformed UTF-8 `text`
  (`bytes_to_text` of invalid sequences): runtime/compiler lane.
- Windows file provider: no POSIX mode bits (chmod is Unix-only), CRT append
  creates absent paths on empty append, no descriptor access-mode enforcement,
  write-only read collapses to EOF: runtime lane if Windows-parity providers
  are ever wanted.
- `sosix_proc_usage` remains an honest Windows stub (`valid: false`).
