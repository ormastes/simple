# Startup aspect dynload

**Status:** implemented and gated (2026-08-24).
**Gate:** `sh scripts/check/check-startup-aspect-dynload.shs` — `PASS — 9 case(s) checked, ...`
**Runtime:** `src/runtime/runtime_native.c` (`__simple_startup_before_main`)

A native Simple program can load custom shared libraries **at startup, before any
user code runs**, and call an entry point in each one.

```sh
SIMPLE_STARTUP_ASPECTS=/path/libobservability.so ./my_program
SIMPLE_STARTUP_ASPECTS=/path/a.so:/path/b.so ./my_program   # ';' on Windows
```

Each listed library must export:

```c
int simple_aspect_pack_init(void);   /* 0 = ok, non-zero = fail closed */
```

## Where it runs

The compiler already generated an entry closure with a pre-main slot
(`src/compiler/70.backend/backend/llvm_native_link_hosted_support.spl:108-134`):

```c
spl_init_args(argc, argv);
if (__simple_startup_before_main && __simple_startup_before_main(argc, argv) != 0) return 125;
__simple_runtime_init();
/* module initializers */
__simple_main();
```

The slot was declared **weak** and **defined nowhere in the tree**, so it always
resolved to NULL and was silently skipped. This change supplies the definition.
Packs therefore load before the runtime is initialized, before module
initializers, and before `__simple_main` — matching the design's "startup"
activation mode ("before application publication").

## Behaviour

| Situation | Result |
|---|---|
| Variable unset or empty | No packs loaded, program runs normally. Not an error. |
| Pack loads, `simple_aspect_pack_init` returns 0 | Continue to the next pack, then to `main`. |
| Path cannot be opened | stderr names the path and the `dlopen` reason; exit **125**. |
| Library exports no `simple_aspect_pack_init` | stderr names the missing symbol; exit **125**. |
| `simple_aspect_pack_init` returns non-zero | stderr names the pack; exit **125**. |

Failure is **fail-closed and loud**. A pack that was named but did not load never
becomes a silent no-op — that is the silent-nil failure mode this repo bans
(`doc/08_tracking/bug/unregistered_extern_silent_nil_2026-08-01.md`). Loading
stops at the first failure; later packs in the list are not loaded.

Libraries are opened `RTLD_NOW | RTLD_GLOBAL` — unlike `spl_dlopen`, which uses
`RTLD_LOCAL`. A startup aspect pack exists to be visible to the program it is
woven into.

## Why the definition lives in `runtime_native.c`

This is load-bearing, not tidiness. A **weak undefined** reference does not pull
a member out of a static archive. A definition in its own new translation unit
would never be linked, and the hook would stay NULL — measured, not assumed: a
probe `main` whose only reference to the runtime was the weak one linked cleanly
and silently skipped the hook.

`runtime_native.o` is pulled into the link because the same generated `main` also
strongly references `spl_init_args`, `__simple_runtime_init` and
`__simple_runtime_shutdown`, which that TU owns. Once the member is in the link,
the weak reference binds. **Moving this function to another file silently
disables it**, which is why gate case 9 pins its placement.

## Relationship to the aspect/facet design

`doc/05_design/language/aop/aspect_facet_dynload_smf_pack_design_2026-08-04.md`
describes an aspect catalog with per-route activation modes, of which `startup`
is one (§9.4; Phase 6 "load startup packs before application publication";
fail-closed startup, §20).

This change implements **only the runtime primitive** underneath that mode: a
process-level list of shared libraries loaded and initialized in the pre-main
slot. It does **not** implement the SMF aspect-pack format, `AspectCatalog`
serialization, profile selection, pointcut routing, or advice weaving.
`src/lib/common/facet_registry.spl` remains an in-memory catalog that marks
aspects loaded without any I/O, exactly as its header states. When catalog-driven
loading is built, it can route its `startup` entries through this primitive
instead of inventing a second loader.

For **on-demand** (non-startup) loading from Simple code, the existing userland
API is `src/lib/nogc_sync_mut/sffi/dynamic.spl` (`DynLib.open` / `try_open` /
`sym`). This change adds no second userland API.

## Limits

- Hosted native binaries only. The generated `main` guards the call with
  `#if !defined(_MSC_VER)`, so MSVC builds do not call the hook.
- Only the hosted C entry closure calls the hook. The three pure-LLVM entry
  variants in `src/compiler/70.backend/backend/entry_point.spl:43,94,142` emit
  `__simple_runtime_init` but **no** pre-main call, so a program built through
  those lanes ignores `SIMPLE_STARTUP_ASPECTS`. That is pre-existing — those
  variants never had the slot — and gate case 8 pins only
  `llvm_native_link_hosted_support.spl`. Probing an `entry_point.spl` lane and
  seeing no pack load is expected, not a bug.
- The path list is read from the environment. There is no manifest or config
  file wiring yet — that arrives with the aspect catalog.
- The gate builds against `build/simple-core/libsimple_runtime.a`, replacing the
  recompiled `runtime_native.o` inside a private copy. It reports
  `ERROR — nothing was checked` if that archive is absent.
