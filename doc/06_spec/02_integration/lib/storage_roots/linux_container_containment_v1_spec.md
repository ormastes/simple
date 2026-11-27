# Retained Linux containment observation refusal

Status: **AUTHORED_UNRUN**. This manually authored mirror is not generated docgen
or runtime evidence. Source: `test/02_integration/lib/storage_roots/linux_container_containment_v1_spec.spl`.

1. **Reject invalid process and binding before native capture.** Actual facade
   rejects invalid PID and digest without an owner or population snapshot.
2. **Capture an actual process with an unrelated cgroup and retain uncertainty.**
   Core-C publishes a partial owner; the actual current process cannot qualify
   the unrelated/private-namespace scope. Owner absence fails, never skips.
3. **Observe the same failed capture without synthesizing emptiness.** Error
   keeps the owner; no `EmptySnapshot` or capacity-release fact is fabricated.
4. **Close observation ownership without a workload or capacity receipt.**
   Successful retirement removes only observation descriptors. Unexpected owner
   turns remain retained before assertions.

The separate authored C fixture uses the actual public native registry, a real
owned child (parent alone releases/reaps exit 17), strict event parser negatives,
wrong binding/kind/stale tokens, and an injected close error after actual close.
The latter verifies permanent uncertainty and no repeated close of a consumed FD.
Neither fixture has been built or run. They do not test positive private PID/
cgroup namespaces, live Podman association, descendants, removal ordering,
no-repopulation, recovery, Windows containment, Simple ABI or capacity release.

## Kernel observation extension (authored, not executed)

**Retain the actual failed capture through kernel profile observation.** The
third scenario obtains an actual partial native owner for an unrelated cgroup,
then calls the production kernel observer with a valid profile. It requires no
facts, an explicit error, and the same retained cleanup authority; successful
close retires only descriptors. Unexpected owners are retained before assertions.
No missing native provider becomes a pass. This is a refusal/ownership scenario,
not positive running-kernel or terminal qualification.
