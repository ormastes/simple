# MCI-v2 Rendering Evidence Producer

## Live collector command owner

`scripts/tool/collect-mci-v2-rendering-live.shs` is the production collection
owner. Its live mode alone executes the canonical bounded Engine2D native build,
the Vulkan showcase/readback run, `renderdoc-evidence.shs capture-simple`, and
the RenderDoc replay gate. The command strings are fixed by the collector and
their exact hashes must be authorized by a
`mci-rendering-live-command-trust-v1` policy for the selected mode and signing
key. Callers cannot substitute an arbitrary shell command.

Each live bundle retains every command receipt, stdout, stderr, raw device
readback, raw `.rdc`, interaction transcript, and performance transcript. Its
signed collector manifest binds run, source, configuration, capture time,
device, driver, queue, exact commands, and every retained artifact hash. The
private collector key signs the manifest; policy pins the corresponding public
key hash and key ID.

Fixture mode executes none of the GPU commands. Its signed manifest always says
`artifact_mode=fixture`, `release_eligible=false`, and
`nonpromotable_reason=contract-fixture-no-gpu-execution`. It is useful only for
the host-independent interface contract and cannot be supplied as live proof.

The frozen adapter vocabulary is `mci-rendering-raw-v1`: `packed.events`,
`composition.bin`, `gui.drawir`, `web.drawir`, `cpu.rgba`, `device.rgba`,
`backend.env`, `queue.env`, `frame.rdc`, `replay.log`, allocation/queue/inflight
event streams, overflow before/after bytes, fallback events, DrawIR entries,
interaction events, frame-time samples, and RSS bytes. The adapter
`scripts/tool/adapt-mci-v2-rendering-bundle.shs` accepts no substitute names and
recomputes the canonical 17 semantic rows. It emits the matching producer trust
policy with exact `adapter:derive:<row>` command hashes.

Run `test/01_unit/scripts/mci_v2_rendering_producer_contract_test.shs` for the
host-only contract. It does not execute a GPU or claim hardware evidence.

The signed collector manifest contains exactly 17 rows. Each binds a canonical
command receipt and raw artifact by SHA-256, plus provenance, measurement, and
negative-control identity. Command receipts have fixed per-row command IDs and
repeat run/source/configuration identity. The RenderDoc row additionally binds
the raw `.rdc` and replay transcript hashes in the signed manifest.

The producer independently checks packed/sealed generation identity, exact
command/glyph/image counts, and composition hash; GUI/Web DrawIR hash equality;
Engine2D generation ownership; exact CPU/device pixel hash equality; device and
queue/submit/fence IDs; the first four retained `.rdc` bytes and correlated
replay transcript; arithmetic `used <= policy limit` and exact `limit + 1`
rejection; unchanged active-state hashes on pre-publication overflow; zero
fallback and DrawIR atlas/cache counters; the exact focus/key/pointer/click
interaction set; and recomputed p95/p99/worst latency plus RSS. Signed policy
also fixes the nominal-exact load profile, command/glyph/image/queue/in-flight
limits, deadline, deadline-plus-one rejection, and resource budgets.

All collector inputs are ABA-snapshotted. The collector key must match an
explicit live or fixture trust policy, with run/source/configuration/device and
a maximum 24-hour lifetime bound by its signature. Every accepted command,
raw artifact, `.rdc`, and replay transcript is retained through the shared
openat/O_NOFOLLOW/fsync publisher under the aggregate root.

`--contract-fixture` emits `CONTRACT_ONLY`, never an aggregate receipt. A live
run requires every row and raw artifact to pass; unavailable hardware remains
`BLOCKED`. Only that live path emits `receipts/rendering.unsigned.template` for
external signing. The aggregate resume row enumerates all manifest, trust,
identity, and time prerequisites and does not imply they are already present.
