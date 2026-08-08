# Task #62 — dlopen Conversion Lanes (link-bound native libs)

Status: plan (dispatch document). Work-list authority:
`doc/04_architecture/runtime/native_library_binding_survey.md` — **that survey
is an adequate work-list and is NOT duplicated here**; this doc adds only the
dispatch layer (lanes, gates, sabotage). Read the survey §2 (reference
patterns), §5 (defect), §9 (order) before starting any lane.

## Ground rules for every lane (non-negotiable)

1. **File ownership is exclusive.** A lane writes ONLY the paths in its "Owns"
   list. If a lane needs a change in a file it does not own, it files a note in
   its report; the owning lane makes the change.
2. **Gate discipline:** capture the full run to a file; the authoritative
   receipt is the stderr/stdout line
   `SPEC FILE VERDICT: <path> declared>=N executed=N passed=N failed=N dropped=N`.
   Match with `/usr/bin/grep -a "SPEC FILE VERDICT"` (ANSI-wrapped; never
   `tail -1`). Pass = executed meets the lane's floor AND failed=0 AND
   dropped=0. Run with `--no-cache --no-cover-check`. Exit status is fail-open
   (unresolved `use` is a WARN, exit 0); exit 255/143 with no output =
   timeout/kill, not a verdict. No bare `assert`; no `check(true)`; `pending()`
   never satisfies a floor.
3. **Sabotage check mandatory** before declaring done: apply it, confirm
   `failed>=1` (or the floor breaks), revert, re-confirm green. Green under
   sabotage = lane FAILURE.
4. **Engines:** each gate states which engine it covers.
   `SIMPLE_EXECUTION_MODE=native` IS NOT A MODE — anything but `interpret`
   silently means JIT. Native coverage requires an actual `native-build`
   artifact executed directly.
5. **`-z muldefs` makes duplicate C symbols silent, not fatal.** A clean build
   proves nothing about collisions; use `nm` on the produced artifact.
6. **Positive probe for binary identity.** Deployed `bin/simple` may be a stale
   seed. Before trusting any gate, prove capability positively (e.g. the probe
   spec itself must FAIL when its subject is sabotaged — never trust banner or
   size). Rebuilding the seed is slow (~20+ min); budget it in N0 only.
7. Commit + push per lane immediately on green (plumbing CAS per
   `.claude/rules/vcs.md`); grep-verify file content before committing — a
   parallel process can revert files mid-session.

## Loader contract (frozen — resolves the design question once)

Every conversion copies the **`gui_renderer.spl:96-144` shape**, not just the
ROCm loop:

1. `spl_dlopen` over an ordered soname candidate list (survey §2/§3 lists the
   candidates per lib — use those verbatim).
2. **Verify EVERY expected export** via `spl_dlsym` before reporting the
   library available. A successful `dlopen` alone is the false-success shape
   this campaign exists to kill.
3. On any missing export: report specific unavailability **naming the missing
   symbol and the soname tried**. No substitute behavior, no fake handles.
4. Resolve once, cache function pointers; never `dlsym` per call on a hot path.
5. **Macro trap:** before binding a name, confirm it is a real dynamic export
   (`nm -D <lib> | grep <name>`). `SDL_BlitScaled` was a macro — a naive
   `dlsym` binds NULL and crashes. Macro-only names must be reimplemented in
   terms of real exports inside the C shim.
6. **Source-list trap (the SDL2 root cause):** a new `runtime_<lib>.c` must be
   added to the default source list at
   `src/compiler/70.backend/backend/runtime_compiler.spl:268` AND to the seed's
   build (`build.rs`) — absence from the source list, not registration, was
   SDL2's actual problem. Each lane below explicitly checks this.

## Lane graph

```
Now:        N0 dup-spl_dlopen defect     N2 renderdoc     N3 OpenCL
After N0:   N1 rt_winit_buffer_*
Not yet:    cranelift/rapier2d/wgpu backends, batch C-ABI libs, D3D11/DXGI
```

N2/N3 do not route through the duplicated `spl_dlopen` from compiled code in a
way N0 changes semantically (they add C-side dlopen), so they may run
concurrently with N0. N1 binds via `spl_dlopen` from `.spl` and waits for N0.

---

## N0 — Single `spl_dlopen` definition (survey §5 defect)

**Value/risk:** every conversion routes through this primitive; two
incompatible string decoders behind `-z muldefs` produce silent dlopen
failures indistinguishable from missing libraries. Highest leverage, small
diff.

**Owns:** `src/runtime/runtime_native.c` (ONLY the three duplicate definitions
at `:5685` `spl_dlopen`, `:5697` `spl_dlsym`, `:5709` `spl_dlclose`),
`src/runtime/runtime_dynload.c`,
`scripts/check/runtime_bundle_duplicate_symbols_baseline.txt` (ONLY lines
listing `spl_dlopen`/`spl_dlsym`/`spl_dlclose`, currently `:74-76`),
`test/01_unit/runtime/dynload_probe_spec.spl` (new).

**Task (fixed procedure — no judgement needed):**
1. Write the probe spec FIRST: `spl_dlopen("libm.so.6")` → non-zero handle;
   `spl_dlsym(handle, "cos")` → non-zero; `spl_dlopen("libdefinitely_absent_xyz.so")`
   → zero/failure (honest negative); `spl_dlclose` succeeds. Run it under BOTH
   `SIMPLE_EXECUTION_MODE=interpret` and as a `native-build` binary. Record
   both verdicts as the baseline.
2. Confirm empirically which duplicate wins today:
   `nm <built runtime bundle> | /usr/bin/grep -c " T spl_dlopen"` and compare
   the disassembled callee (survey's "runtime_native wins" is an inference,
   NOT confirmed).
3. Delete the three `runtime_native.c` duplicates so `runtime_dynload.c` holds
   the only definitions (flags `RTLD_NOW | RTLD_LOCAL`).
4. Re-run both probes. If the native probe goes RED, the decode in
   `runtime_dynload.c` is wrong for compiled callers: switch its string decode
   to `rt_core_string_to_cstring` and re-run BOTH. Acceptable end state: ONE
   definition, both probes green. If both decoders are genuinely required by
   engine, keep one exported function that the build selects via existing
   compile-time guards already present in those files — do NOT reintroduce a
   duplicate strong symbol.
5. Remove the three lines from the duplicate-symbols baseline; the baseline
   may only shrink.

**Gate (engines: interpreter AND native):**
```
SIMPLE_EXECUTION_MODE=interpret bin/simple test test/01_unit/runtime/dynload_probe_spec.spl \
  --no-cache --no-cover-check > /tmp/n0i.log 2>&1; /usr/bin/grep -a "SPEC FILE VERDICT" /tmp/n0i.log
```
plus the same spec compiled via `native-build` and executed directly.
Receipt: each run `failed=0 dropped=0 executed>=4`. Additionally
`nm` on the rebuilt bundle shows exactly ONE `T spl_dlopen`.
**Sabotage:** (1) make `spl_dlopen` return a fixed non-zero for the absent-lib
probe → honest-negative assertion RED; (2) reintroduce one duplicate
definition → the `nm` count check RED. Both individually.
**Size:** 1 agent-session + one seed/runtime rebuild (budget the rebuild).
**Status: dispatchable now.**

## N1 — `rt_winit_buffer_*` (13 syms; survey §1 confirmed instance)

**Blocked by:** N0.

**Owns:** `src/runtime/spl_winit/src/lib.rs` (add the 13 `rt_winit_buffer_*`
`#[no_mangle]` exports — a software framebuffer atop the existing winit
surface),
`src/compiler_rust/compiler/src/interpreter_extern/winit_sffi/winit_sffi_buffer.rs`
(replace lying stubs: route to the cdylib when loadable, else return honest
failure — `rt_winit_buffer_present` must NEVER return `true` without a real
surface), `test/01_unit/runtime/winit_buffer_honesty_spec.spl` (new).

**Task:** enumerate the 13 names from `winit_sffi_buffer.rs` (that file is the
authoritative list); implement each in the cdylib; the `.spl`-side loader is
already correct (`gui_renderer.spl` verifies exports) — after this lane its
export check starts passing for the buffer family. Note `rt_winit_*` sits
behind the seed's `gui` cargo feature (`mod.rs:2551`): the gate must run a
seed built WITH that feature; state in the report which build was used.

**Gate (engine: seed interpreter; host has `DISPLAY` unset — honest-failure
assertions are the point, not pixels):** spec floor `executed>=6`:
create/present WITHOUT a display → structured failure (not `true`, not a fake
id); with cdylib file absent (rename it in a temp copy of `build/sffi/`) →
unavailability message naming the missing export; message text asserted (prove
by which error text CHANGES — before this lane it is a stub success).
**Sabotage:** restore `rt_winit_buffer_present` stub returning `true` → RED.
**Size:** 2 agent-sessions (Rust cdylib work + rebuild).
**Status: blocked by N0.**

## N2 — `rt_renderdoc_*` (10 syms; link-bound AND undefined — lying twice)

**Owns:** `src/runtime/runtime_renderdoc.c` (new),
`src/compiler/70.backend/backend/runtime_compiler.spl` (ONLY the source-list
line `:268` and the object list near `:291` — add `runtime_renderdoc`),
the build file lines currently carrying `-lrenderdoc` (locate:
`/usr/bin/grep -rn "lrenderdoc" scripts/ src/ --include='*.shs' --include='*.rs' --include='*.spl'`
— remove the hard link), `test/01_unit/runtime/renderdoc_honesty_spec.spl` (new).

**Task:** RenderDoc's in-application API has exactly ONE real export:
`RENDERDOC_GetAPI`. Per-symbol dlsym of anything else binds NULL (the macro
trap in its purest form). Shape: `spl`-visible `rt_renderdoc_*` functions in
the C shim; on first use dlopen `librenderdoc.so` (already-injected process
module: try `dlopen(NULL)`-style lookup first — RenderDoc is normally
preloaded), dlsym `RENDERDOC_GetAPI`, obtain the versioned function table,
implement the 10 `rt_renderdoc_*` in terms of it. All 10 report honest
unavailability when the lib is absent (it IS absent on this host — that is the
gate's main path).
**Gate (engines: interpreter + JIT — state both):** floor `executed>=5`; every
symbol returns structured unavailability on this RenderDoc-less host; no fake
capture handles; before/after error-text change asserted (was: unknown extern
/ link failure). **Sabotage:** make `rt_renderdoc_is_available` return 1 when
`RENDERDOC_GetAPI` was never resolved → RED.
**Size:** 1–2 agent-sessions. **Status: dispatchable now.**

## N3 — OpenCL (link-bound; broken on this very host — survey §7)

**Owns:** the OpenCL binding C file(s) (locate via
`/usr/bin/grep -rln "lOpenCL\|clGetPlatformIDs" src/runtime scripts/check`),
`scripts/check/check-opencl-generated-2d-readback.shs` (drop `-lOpenCL`),
`test/01_unit/runtime/opencl_honesty_spec.spl` (new).

**Task:** ROCm-style candidate loop (`libOpenCL.so.1` → `libOpenCL.so` →
`OpenCL.dll`), export-verify the cl* entry points actually used, resolve-once.
Host truth baked in: this host's ICD is CUDA-bundled and enumerates
`platform=1 context=0` headless — the gate asserts context-creation failure is
reported as a specific OpenCL error, not as "library missing" and not as
success. **Gate (interpreter + JIT):** floor `executed>=4`; distinguishes
three states in asserted text: lib absent / lib present but context fails
(this host) / context ok. **Sabotage:** collapse the three states into one
generic failure string → text assertions RED.
**Size:** 1 agent-session. **Status: dispatchable now.**

---

## Judged NOT worth a lane now (one line each)

- **`rt_cranelift_*` (77)** — needs a JIT backend, not a loader; survey §8.7
  requires a reachability pass first; a dlopen lane here would disguise
  "never written" as "unlinked".
- **`rt_rapier2d_*` (51)** / **`rt_wgpu_3d_*` (18)** — same shape: real
  backend work (a `spl_winit`-style cdylib each); plan only after N1 proves
  the cdylib+honesty pattern end-to-end.
- **SDL2** — already converted (`24bb824cb31`); nothing left but keeping the
  survey row current.
- **Batch C-ABI libs (sqlite3, zlib, zstd, libxml2, tree-sitter, ncurses,
  OpenSSL, libtorch)** — link-bound but ubiquitous, cold, and honest on
  failure (link error, not fake success); convert opportunistically after N0,
  not as dedicated lanes. libtorch additionally needs a C shim first.
- **D3D11/DXGI** — blocked by: no Windows host evidence available; source-only
  claims forbidden by the evidence bar.
- **Metal/Cocoa, libc/libm/libdl/libpthread** — never (survey §3/§4).
