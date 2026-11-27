# Finite local host execution

The user requested implementation of the complete execution plan. This source
slice connects existing enrollment, signed authority, capacity journal and OCI
provider owners. It does not claim that the wider distributed service is complete.

| Requirement | Behavior | Executable coverage |
|---|---|---|
| HOST-LOCAL-01 | One local command core accepts bounded canonical signed inputs; malformed input creates no workload state | `host_local_command_spec.spl` |
| HOST-LOCAL-02 | Acquire real machine, boot and approved provider identity; compare retained enrollment on reopen | `host_local_command_spec.spl`; live platform qualification pending |
| HOST-LOCAL-03 | Retain interrupted claims and refuse edited/foreign roots before capacity opens | `host_local_command_spec.spl` |
| HOST-LOCAL-04 | Persist original request, signed execute packet and execution intent before provider effects | signed execution spec in this slice |
| HOST-LOCAL-05 | Return updated owners on every effect outcome; preserve charged uncertain capacity | signed execution spec in this slice |
| HOST-LOCAL-06 | Report successful execution only after independent exact native inspection and retained observation under explicit process-crash journal profile | signed execution spec; live platform qualification pending |
| HOST-LOCAL-07 | Inspect never creates/starts work; prepared, unknown and observed runtime facts stay distinct | signed execution spec and local command core |
| HOST-LOCAL-08 | Windows Docker and Linux Podman route through the shared Simple Container lifecycle API; host core has no direct backend dispatch | shared facade connected; wrong-backend refusal authored; Windows persistent startup and native qualification pending |
| HOST-LOCAL-09 | Verify a request/action-bound absolute authority deadline after provider identity checks, immediately before native effects | shared typed deadline wired; native-boundary prevention authored NOT_RUN |

Production qualification remains NOT_RUN until the admitted compiler, real
rootless Podman platform and signed end-to-end scenarios are exercised. No seed
compiler, scripted native evidence or previously timed-out build substitutes for
those gates.
