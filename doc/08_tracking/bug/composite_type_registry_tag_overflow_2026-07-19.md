# Bug: composite type registries cross encoded tag ranges

## Status

Source-fixed. A bounded current-source LLVM probe filled the union and tuple
ranges, rejected the next unique payload and negative getters, reset tuple
state, and exited `0`. The canonical `expect` spec compiled with zero failed
modules; example execution remains pending a usable pure-Simple test runner.

Union, intersection, refinement, and tuple registries appended every
annotation without interning or checking their numeric range. The 101st union
was therefore classified as an intersection, and the 1001st tuple as a generic
array. Tuple state was also omitted from `reset_all_pools()`, while every
registry getter accepted negative IDs.

All seven encoded registries now reuse exact ordered payloads before checking
their existing fixed capacity, return `-1` instead of entering the next
namespace, and reject negative getter IDs. Tuple reset is included. Parser
callers report union/tuple exhaustion and fall back to their bare safe type,
matching existing Dict/Result handling. Exact member order and refinement
predicate text remain observable; no canonical sorting or normalization was
added.

The focused regression fills every range to its last valid slot, rejects the
next unique payload, checks fresh-literal interning and negative getters, then
resets and requires every first tag to return to its family base.
