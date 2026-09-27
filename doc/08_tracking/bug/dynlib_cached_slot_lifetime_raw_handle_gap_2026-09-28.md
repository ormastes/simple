# Cached SFFI slots and raw handle ownership are not yet unified

**Status:** Open. The `fix/sffi-cached-slot-lifetime-20260928` draft is a
candidate, not release evidence.

## Evidence

`DynI64FnSlot` retains a raw function pointer after `DynLib.close()` unloads its
provider. A copied or retained slot can therefore call unmapped code. The
candidate introduces a revocable mapping identity and defers `dlclose` until
admitted calls finish, but the existing raw API still exposes `DynLib.handle`.

`chromium_reference_oracle_sffi.spl`, `chrome_render_module_sffi.spl`, and
`ui/gui_renderer.spl` obtain that handle through `DynLib.load()`, retain raw
addresses in their own structs, then close directly with `spl_dlclose`.
`wffi_into_bytes_spec.spl` does the same in tests. Those closes bypass the
candidate owner, leaving an entry that appears live after the native mapping
is gone. `backend_plugin/dynamic_loader.spl` also exposes the raw handle to a
tagged transport, although its own close path calls `DynLib.close()`; its
in-flight transport lifetime must be covered before retiring that mapping.
The draft routes GPU/GUI closes through `DynLib.close()`, retains `DynLib` in
their handles, and reserves a mapping use around cached native calls. The
backend tagged transport reserves one use across a single call or the complete
open/compile/finalize/close batch. These edits still need source-matched
compilation and lifecycle tests before promotion. The GUI window/event-loop
objects remain main-thread resources; the mapping lease alone does not make
concurrent GUI object destruction safe.

The Chromium bindings also own provider session objects separately from the
library mapping. A mapping lease keeps function code loaded, but it does not
stop `chromium_oracle_release` or `chrome_render_release` from destroying a
session while another retained handle uses it. Session teardown needs its own
drain/refusal rule before concurrent release can be claimed safe.

## Session teardown repair boundary

The session owner must serialize **admission**, not execute provider code while
holding its mutex. A session moves from `Idle` to `Calling` for one admitted
foreign call, then back to `Idle`; `Idle` may instead move to `Destroying` for
exactly one release. Calls and releases observing `Calling` or `Destroying`
refuse without entering the provider. A busy release leaves the session live
for a later retry. The owner keeps a mapping use for the entire native session
lifetime, so closing a copied `DynLib` cannot unload its destructor before
session cleanup. The destructor runs on the releasing thread after the owner
has claimed it, and the lifetime use ends only after cleanup.

The oracle creates one session per loaded library, so its handle can carry a
never-reused owner identity while the owner retains the raw session address.
Chrome render returns a raw `i64` session address today. A replacement session
may reuse that address, allowing a stale copied caller to act on the new
session. The facade must instead return a never-reused positive ticket and map
that ticket to the native address inside the owner. Its existing showcase
callers pass the value opaquely; the ticket contract still requires explicit
documentation and tests. Releasing one render session must not unload another
live session from the same provider.

Do not hold the owner mutex across a foreign call: a reentrant provider would
deadlock. Do not defer native destruction to the last calling thread: that
changes synchronous release semantics and may violate provider thread
affinity. The mapping owner alone cannot establish either session guarantee.

The candidate's owner takes a mutex on every cached-slot call. The selected
environment variant NFR-003 forbids a lifecycle lock in dense provider batch
dispatch and limits its overhead to 2% against a direct reference batch call.
The draft `native_callable_owner_v1` batch API reserves one use for the whole
batch; the scalar path still takes a mutex per call. No latency, allocation,
or RSS comparison for the draft has been run.

## Acceptance

1. One owner closes each mapping exactly once, including raw GPU, GUI, and
   tagged backend transport paths, while stale slots and stale aliases return
   a typed refusal.
2. An admitted call survives concurrent retirement and the final use closes
   the mapping. New calls fail after retirement.
3. Versioned and convention loader caches never return retired entries.
4. A source-matched pure-Simple runtime runs the native fixture and lifecycle
   tests. The checked dispatch meets NFR-003 on its named batch fixture with
   no per-element lifecycle lock or allocation.
5. A blocking native fixture call makes a concurrent release return busy without
   destroying or unloading its session; after the call finishes, release
   succeeds. Two releases destroy exactly once, and reentrant release refuses
   without deadlocking.
6. A stale copied handle or ticket cannot call or destroy a replacement
   session. Destroying one render session leaves another admitted session
   callable; closing a library alias cannot unload either session before its
   cleanup.
