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
Until these are decided, `--xray` stays refused on Windows at the driver, so a switched-on DLL
cannot yet be built end to end; the on-vs-off wall time is therefore not measured.
