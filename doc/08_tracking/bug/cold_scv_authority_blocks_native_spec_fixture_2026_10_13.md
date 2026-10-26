# Cold SCV authority times out before a canonical native spec fixture

Status: reproduced; root cause not profiled. Bug DB reconciliation pending.

An actual native worker compiled and linked an authored Hello through canonical
policy/SCV authority, and its executable printed the expected message with exit
0. The next unchanged canonical fixture,
`test/fixtures/lib/spec_facade_control.spl`, could not reach native compilation:
the Phase1 bootstrap adapter spent its entire 180-second budget acquiring cold
source authority for its coherent library projection.

## Reproduction and authority

- Original source revision: `cce267e717684e7f87aea1603df3da7c0745258d`.
- Projection: 8,658 original `src/lib` files plus the original fixture,
  55,310,439 bytes. These are source files, not test-case counts.
- Private Git commit: `054eb3c76db3194a4a2d40964751872924cbaecb`.
  All 8,659 original Git blob IDs and modes match the frozen source manifest.
- Bootstrap adapter producer SHA-256:
  `d95807daf8725254e6737f12b0a81965ac5ae0a9236b19eedac94940bd9867f1`.
- Actual APIs: `environment_variant_policy_handoff_prepare_from_snapshot_v1`,
  attach, and `compiler_source_authority_acquire_v1` with source roots
  `src/lib` and `test/fixtures/lib`, then publish/reopen if acquisition succeeds.
  Real environment and absent project/user configuration checks precede the
  handoff. No serialized policy or source-identity stamps were fabricated.
- Runner: `build/native_probe/core-c-worker-profile-20261013-sol/run_spec_authority_v2.py`,
  SHA-256 `c7132d85695249006d99e3f60be32cadc94f6e32d2dd6faa8aecaf2ecbf22beb`.

The first private Git preparation used an unanchored `build/` ignore, excluding
nine nested library owners from its index. Pre-dispatch blob/mode verification
caught this. A new private commit anchored `/build/` and `/.simple/` and retained
all nine original files. No authority/compiler invocation used that incomplete
commit; its failed preparation audit is preserved separately.

## Actual result

One authority invocation timed out with exit 124 and final Job active count 0.
Observed peak was 1,223,572 KiB. Its 158 observed source reads were confined to
the authenticated closure; all seven required policy/authority owners were
observed, with no changed input pins or outside reads. No forwarded policy args,
published SCV environment, inventory CURRENT pointer, or snapshot were produced.
The fixture's native receiver was never invoked. Its authored cases remain
unrun; none of the six required subsystem products is qualified by this result.

Evidence root:
`C:/p3/build/native_probe/core-c-worker-profile-20261013-sol/spec-facade-native-gate/authority-attempt/`.

- `RESULT.json`: `8922ff2625497f2e0c957d9235418715e3f8ea669f2cc5c2cde6e6cd8b963a71`
- `receipt.env`: `d9edc9e7909b9948c4ca7e3c90cdece03dd8a44af351be2e35f4037eed15bcd6`
- `parent.log`: `9dc3cf03086d40d5ccd4e208c2d44fe1958edd82816d88997aa3f84866b5fe02`

## Source-backed investigation

The frozen `inventory_events.spl` cold branch issues one Git listing, then
constructs an event for each admitted file. `inventory_scratch.spl` reads each
file under a transient scope. `compile_source_inventory_core.spl` builds
normalized semantic, export, initializer and provider views and computes up to
five digests, reusing equal-view digests. `sha256_text` already attempts the
runtime accelerator and records fallback; the trace does not establish that
the fallback ran. Repeated array transfer/copy and text normalization are
candidates for measurement, not proven causes. This path does not issue a Git
command for each file.

Keep the original snapshot inputs and failed cache. Measure the actual cold
owner before choosing a repair or a compiled authority adapter. Preserve every
source/identity validation and canonical publication gate. Do not publish a
reduced or invented inventory to bypass this timeout, and do not repeat the
unchanged invocation merely with a larger time limit. This is the first dynamic
cycle of this fixture authority feature, not a failure of the already-passing
native Hello compilation or a native compiler performance measurement.
