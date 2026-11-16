# XRay Windows flag-guard route: decisions needed before the leaf and admission steps

Date: 2026-11-14
Status: open (lane xrayfg stopped here by its stop condition: design not in the plan doc)

Done and GREEN (`xray_llvm_attrs_spec.spl` 22/22): the IR half. For a Windows target and
`xray_mode>0` the LLVM translator emits, per sled function, `@__simple_xray_slot_<sym>`
(`internal global i8 0`), a volatile-load/icmp/br/call guard at entry (kind 0) and before every
`ret` (kind 1), one exported `@__simple_xray_descriptor_v1 = { i64 count, [count x ptr] }`
(site id = index), and an exported hook pointer `@__simple_xray_hook_v1` behind a DLL-local
`__simple_xray_edge_v1` (so the DLL links with no undefined host symbol). Off emits no xray text.

Open decisions (not in `xray_v1_integration_status_2026-11-03.md`, which names the route but
not these):
1. Leaf binding: how Simple code locates and stores into the slots of a loaded DLL
   (`rt_host_dynlib_symbol` of the descriptor, then a raw byte store extern; which extern, and
   does `rt_host_dynlib_*` expose enough to write a data slot).
2. Handler ABI: what the host stores in `__simple_xray_hook_v1`; it must be a Simple-owned
   function reaching the shared record/profile fold, whose signature is `(i64 site, i32 kind)`.
3. New `TraceBackendV1` member (and sled-kind value) for the flag-guard leaf, and the
   `TraceBuildRouteKindV1` value; admission in `observer_build_route_v1.spl` and
   `driver_xray_policy.spl` for `x86_64-pc-windows-gnu`/`-msvc` + llvm only.
4. Site-id to function-name map for the profile: descriptor carries slots only.
## Decisions (2026-11-15, lane xrayleaf) — each PROVISIONAL (owner to ratify)

Status: verification-pending for items 1, 3, 4; item 2 hook ABI chosen, host half replaced by ring mode (below, PROVISIONAL).

1. **Leaf binding — PROVISIONAL (owner to ratify).** `rt_host_dynlib_symbol(handle, name)` resolves
   `__simple_xray_descriptor_v1` / `__simple_xray_hook_v1` on the loaded DLL; slots are read with
   `rt_ptr_read_i64` and set/cleared with `rt_ptr_write_u8` (both already backed in the runtime and
   the interpreter registry; no new extern). Implemented in
   `src/lib/nogc_sync_mut/trace/xray_win_flag_leaf_v1.spl` (`XrayWinFlagLeafV1`, port
   `XrayWinModulePortV1`, host port `XrayWinDynlibPortV1`). Adapter ids are 1-based; descriptor and
   hook sites are 0-based (`id - 1`). Rejected: a new `simple_xray_win_*` C shim per slot op — more
   surface, and the existing raw-pointer externs already store a data byte.
2. **Handler ABI — PROVISIONAL (owner to ratify).** The hook holds a C-callable `void(i64 site, i32 kind)`
   (exactly what #9281 emits), whose body is the pure-Simple `xray_win_edge_record_v1`: one raw-edge
   record into the resident channel via `trace_native_channel_record_words_v1` (kind 0 -> Entry,
   1 -> Exit, function/site id = site + 1). Rejected: a richer `(ctx, site, kind)` ABI — needs an IR
   change and a second data cell for no current consumer. **BLOCKED:** nothing mints a C-callable
   address for a Simple function from an interpreted host, so `XrayWinDynlibPortV1.handler_address()`
   is 0 and `install()` fails closed. Unblocking needs the handler compiled into native code (a
   natively built host, or the handler emitted beside `__simple_xray_edge_v1`) — a heavy build, not
   done in this lane.
3. **Backend / route — PROVISIONAL (owner to ratify).** No new `TraceBackendV1` member: the leaf reports
   `Llvm` (same compiler-emitted LLVM sled family; only the leaf differs). One new
   `TraceBuildRouteKindV1.WindowsLlvmFlagGuardCandidate`, for `x86_64-pc-windows-gnu` /
   `x86_64-pc-windows-msvc` + Dynamic + Auto/Llvm only; admitted in `xray_observer_request_admit` only
   with `--xray` (else InstrumentationAbsent) and backend `llvm` (else UnsupportedTarget). Rejected: a
   `TraceBackendV1.LlvmFlagGuard` member — it would fan out through every backend match and the
   adapter's backend/leaf coherence check for a distinction the route already carries.
   Not lifted: `driver_target_trace_capability_v1` (automatic debug-observer receipt gate), which by its
   own comment needs the runtime admission owner's receipt, not a route candidate.
4. **Name map — PROVISIONAL (owner to ratify).** Exported `@__simple_xray_names_v1 = { i64 count,
   [count x ptr] }` parallel to the descriptor, entry i = private NUL-terminated C string of the
   Simple function name of site i (`escape_llvm_string`). Read by `xray_win_site_name_v1`. Rejected:
   a sidecar map file — a second artifact to keep in sync with the DLL.

Specs: `xray_llvm_attrs_spec` 24/24, `xray_win_flag_leaf_v1_spec` 7/7, `observer_build_route_v1_spec`
9/9, `xray_observer_admit_spec` 6/9 (the 3 failing CompileContext examples are Linux-target and fail
with `TARGET-PROFILE-E-UNAVAILABLE` from the unchanged receipt gate above; not re-run on the base). Off identity: an
`xray_mode=0` Windows module still emits no `xray` text (attrs spec). The two system specs stay
BLOCKED on Windows (ELF-lane gate, plus item 2).

## Ring mode (2026-11-15, lane xrayring) — PROVISIONAL (owner to ratify)

Item 2's BLOCKED host half is removed for the pure-Simple host by recording inside the DLL:
`@__simple_xray_ring_v1 = { i64 capacity (65536), i64 write index, i64 dropped,
[capacity x { i64 site, i32 kind, i32 pad, i64 seq }] }`. With a null hook,
`__simple_xray_edge_v1` claims an index by `atomicrmw add` (monotonic), drops and counts
(`atomicrmw add` on dropped) when the index is past capacity, writes site/kind and
release-stores `seq = index + 1` last. The hook path is unchanged. The ring never wraps
(fixed-size; no reset while edges may run — lockless, no locks). Leaf: `install` succeeds
with no handler when the ring symbol resolves (hook stays null); `drain()` reads records
with `rt_ptr_read_i64`, stops at the first record whose seq is not yet published, and
writes one raw-edge channel record per edge (`xray_win_edge_record_v1`); `ring_dropped()`.
Rejected: a wrapping ring (needs a consumer-index handshake with the DLL for no current
need) and a host-minted C callback (needs a native host build).

Also fixed: the xray globals are no longer `dllexport` — one explicit export turned MinGW
lld auto-export off and the `--xray` DLL lost every function export
(`xray_win_flag_guard_dllexport_disables_mingw_auto_export_2026-11-15.md`). The MSVC
lane (no auto-export) stays open.

Real run, Windows 11 host, seed-attr, llvm-mingw 20260922 UCRT
(`test/fixtures/xray/xray_win_llvm_compile_driver.spl` builds,
`test/fixtures/xray/xray_win_ring_e2e_host.spl` loads via `rt_host_dynlib_open`, patches
`traced`+`add1`, calls through `rt_call_ptr_1`, drains): `RING-E2E PASS`, edges
`E:traced,E:add1,X:add1,X:traced`, `traced(1)=44`, 0 dropped.
Compile wall (one run each, loaded host): xray off 163 s; xray on 114 / 146 / 133 s —
the spread is host noise, no measurable on/off difference. DLL size off 7,680 B, on
1,580,544 B (the nonzero capacity header puts the 1.5 MB ring in `.data`, not `.bss`).
Call time, 5000 calls of `traced`, three reps: xray-off build 2431/3256/2438 us, xray-on
slots off 3310/2303/2546 us, slots on 3675/3521/3636 us (~0.2 us/call more). Calls go
through the seed interpreter's `rt_call_ptr_1`, whose overhead dominates; these are not
native-caller numbers.

Specs: `xray_llvm_attrs_spec` 27/27, `xray_win_flag_leaf_v1_spec` 9/9. The two system
specs stay BLOCKED on Windows (their ELF-lane gate is unchanged; not re-run).
