# AOP match cache retains build-session graphs after teardown

Status: source fix authored; native two-session regression unrun.

The global `AopMatchDriverStateV1` retained selector, shard, single-flight,
plugin descriptor, and traversal-instance dictionaries. Those dictionaries can
receive allocations owned by the live BuildSession. The session end path resets
several compiler registries, but did not clear this AOP root before freeing the
session heap. A later compiler visit could consequently inspect freed graph
storage. This is an ownership defect identified from source, not a reproduced
native crash or a completed production qualification.

The correction makes the global root optional, associates it with a scalar
session ID, invalidates its scalar initialized sentinel before the admitted BuildSession heap-end call, and
creates fresh state lazily under the next owner. The reset does not allocate
replacement dictionaries or boxed None values. The stale slot is not inspected
until a new owner replaces it. Failed shares retain the live session and its cache;
a refused heap-end leaves an uninitialized cache that can safely rebuild. The normal
cache entry requires no active or paused transient scope so scratch-owned
entries cannot escape into the global graph within the same session.

The scalar session comparison occurs before reading the optional state. It is
secondary protection; the explicit pre-free scalar invalidation remains the primary lifetime
boundary. Direct pure APIs taking an explicit caller-owned state continue to
require that caller to own its graph. No cross-session reuse is claimed.

Regression: `test/01_unit/compiler/aop/aop_match_cache_session_lifetime_spec.spl`
uses actual native session begin/end calls and checks two selector-cache epochs.
It is authored but unrun while native probes are held. Full compiler, MCP/LSP,
and daemon integration checks remain unrun. Do not mark the bug verified from
this report alone.
