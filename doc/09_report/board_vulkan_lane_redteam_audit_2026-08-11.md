# Board Vulkan Lane Red-Team Audit (lane L8)

**Date:** 2026-08-11
**Auditor role:** V9 Vulkan red-team (`doc/03_plan/infra/counterpart/counterpart_conformance_parallel_agent_plan_2026-08-09.md`)
**Scope:** L1 (SPIR-V boundary), L2 (device enumeration), L3 (readback gate),
L4 (provider inventory), plus the shared frame (`soc_profile.spl`,
`counterpart_plan.spl`, `board_vulkan_counterpart_plan_spec.spl`).
**Method:** static read of every spec *and* the implementation under it; for each
`it` block, "name the one-line implementation change that makes this fail". Host
commands were run only for provenance checks (`glslangValidator`, `spirv-dis`,
`sha256sum`); no spec was re-run (10-25 min each on this loaded host), and one
lane's file changed under the audit — noted inline.

**Files that changed during this audit:** `boundary_spirv_canonicalize.spl` was
rewritten at 00:49 (mid-audit, after the 00:47 read) and
`boundary_enumeration_provider.spl` at 00:47. All quotes below were re-read
after those writes except where a timestamp is given.

---

## Lane L1 — SPIR-V boundary (`vulkan.shader.spirv_binary@1`)

### L1-F1 (CRITICAL) — the spec has never executed; its green verdict does not exist
**Mode:** 7 MEASUREMENT-TRAP EVIDENCE.
**Evidence:** `.../scratchpad/spirv_spec.log:1931-1946` (run at 00:40):

```
error: compile failed: parse: in ".../board_vulkan/boundary_spirv_canonicalize.spl": Unexpected token: expected pattern, found Use
error: test-runner: no examples executed
SPEC FILE VERDICT: ... declared>=1 executed=0 passed=0 failed=1 dropped=1 unrun=1 reason=parse-error
Results: 1 total, 0 passed, 1 failed
```

The cause was `for use in spirv_line_use_ids(tokens):` — `use` is a reserved
keyword, so the module could not parse and **all 15 `it` blocks were dropped**.
The loop variable was renamed to `used_id` at 00:49
(`boundary_spirv_canonicalize.spl:123`) and a re-run (`spirv_spec2.log`) was
still in flight with no `Results:` line when this audit closed. **As of now L1
has zero passing evidence**, including for its sabotage scenario.
**Fix:** re-run the spec and quote the new `Results:` line before any green claim
(the rename is already in place).

### L1-F2 (HIGH) — dead-value elimination deletes structurally load-bearing instructions, hiding a real defect class
**Mode:** 6 NORMALIZATION THAT HIDES SEMANTICS.
**Location:** `boundary_spirv_canonicalize.spl:128-163` (`spirv_eliminate_dead_values`),
reached from `spirv_canonicalize_lines:204-206`.
The pass drops *any* line with an unreferenced result id — it is not restricted
to value-defining opcodes. Against the real glslang output on this host
(verified live):

```
%1 = OpExtInstImport "GLSL.std.450"     <- result id never used -> DROPPED
%5 = OpLabel                            <- no branch targets it -> DROPPED
```

`OpLabel` is not a value: a function body without one is invalid SPIR-V, and
`OpExtInstImport` is a module-level dependency declaration. Concretely: **delete
`builder.emit_label()` from `boundary_spirv_provider.spl:66` and the candidate
still canonicalizes byte-identically to the counterpart** — I traced both sides
line by line and they match exactly. So a candidate that emits no basic-block
label at all passes this boundary. That is the exact vacuity the "four named
dimensions" docstring promises does not exist; the docstring's own rule
("an opcode or a live operand is never normalized away") is violated by its
own code.
**Fix:** restrict DCE to a whitelist of pure value/type/constant opcodes
(`OpType*`, `OpConstant*`, `OpVariable`, `OpSpecConstant*`) — never `OpLabel`,
`OpExtInstImport`, `OpFunction`, or any control-flow opcode.

### L1-F3 (MEDIUM) — the sabotage's reason-check cannot distinguish a LocalSize divergence from any other
**Mode:** 1 TAUTOLOGICAL ORACLE (partial).
**Location:** `spirv_boundary_glslang_spec.spl:196` —
`assert_contains(detail, "LocalSize")`, where `detail` is built at
`boundary_spirv_provider.spl:134` as the *concatenation of both canonical texts*.
`OpExecutionMode %main LocalSize 1 1 1` is present in both sides on every
successful capture, so this assertion holds whether the divergence was in
LocalSize, in an opcode, or anywhere else. It does discriminate the
capture-failed case (where `detail` is `"candidate unavailable: ..."`), so it is
not wholly vacuous — but it does not verify the *reason* the comparison failed,
which is the entire point of a sabotage.
**Fix:** assert on a diff, not on the concatenation — e.g. have
`spirv_boundary_compare` return the first differing canonical line pair and
assert that pair contains `LocalSize`.

### Sound parts of L1 (stated plainly)
- The counterpart is genuinely *executed*, not transcribed: real
  `glslangValidator` + `spirv-as` + `spirv-dis` subprocesses
  (`boundary_spirv_provider.spl:82-114`).
- Independence grouping is correct: `khronos-glslang`, explicitly not `mesa`
  (`:167`, asserted at spec `:145`) — no FAKE INDEPENDENCE here.
- The artifact hash is computed live from the invoked binary
  (`spirv_glslang_artifact_hash:160-161`); I verified
  `sha256(/usr/bin/glslangValidator) = 96ea85d4…d026`. No placeholder.
- `spirv_boundary_compare` fails closed on either side being unavailable
  (`:124-129`) — no UNAVAILABLE-AS-PASS.

---

## Lane L2 — device enumeration (`vulkan.device.enumeration@1`)

### L2-F1 (HIGH) — no counterpart is executed and no candidate exists; the "boundary" is a comparator unit test
**Mode:** 2 EXPECTED-FROM-ACTUAL / 5 UNAVAILABLE-AS-PASS (structural).
`lavapipe_reference_enumeration()` (`boundary_enumeration_provider.spl:104-137`)
is a hand-typed literal. Nothing in the lane invokes `vulkaninfo`, loads
`lvp_icd.json`, or hashes `libvulkan_lvp.so`; there is no `ProviderManifest`,
no `provider_registry` registration, and no artifact hash anywhere in the lane
(contrast L1 and L4, which both do this). The candidate side is
`candidate_enumeration_status() -> ProviderStatus.unavailable`
(`:93-94`) — a literal return. Consequently **every** comparison in the spec is
fixture-vs-fixture: the reference against a reordered copy of itself, or against
a hand-mutated copy of itself. That validates
`enumeration_records_structurally_equal`, which is worth having, but it is a
unit test of a comparator, not a counterpart boundary.
**Fix:** capture lavapipe at run time (`process_run_bounded` on `vulkaninfo
--json` with `VK_ICD_FILENAMES` pinned) and register a `ProviderManifest` with
`artifact_sha256_of_file(libvulkan_lvp.so)`, exactly as L1 does for glslang.

### L2-F2 (HIGH) — the two "candidate honesty" scenarios assert a constant against itself
**Mode:** 1 TAUTOLOGICAL ORACLE.
`device_enumeration_boundary_spec.spl:228-235` asserts
`candidate_enumeration_is_available() == false` and
`candidate_enumeration_status() == ProviderStatus.unavailable`. Both functions
are one-line literal returns (`boundary_enumeration_provider.spl:93-97`). The
only implementation change that fails these is editing the literal — no change
to `vulkan_icd_virtio.spl` or `gpu_vendor_probe.spl`, the modules the docstring
credits, can affect them. So the spec cannot detect the very regression its
"Recovery and Troubleshooting" section describes ("the candidate started
fabricating enumeration data").
**Fix:** derive the status from the probes — e.g. return `unavailable` iff every
`gpu_vendor_probe` reports `is_available() == false` — so a probe that starts
fabricating a device flips the assertion.

### L2-F3 (MEDIUM) — "ACCEPTS the restored record" is literally `f() == f()`
**Mode:** 1 TAUTOLOGICAL ORACLE.
`device_enumeration_boundary_spec.spl:219-225`: `restored` is a fresh
`lavapipe_reference_enumeration()`, compared against another
`lavapipe_reference_enumeration()`. No implementation change other than making
the comparator non-reflexive can fail it; it does not prove "the gate is not
stuck red" for the sabotaged fields, because the sabotage is never reverted —
it is a different value that was never applied.
**Fix:** restore the *sabotaged* record's dropped queue family explicitly and
compare that reconstruction, so the assertion exercises the mutation path.

### L2-F4 (MEDIUM) — limit magnitudes are dropped, so the transcribed limit values are dead data
**Mode:** 6 NORMALIZATION THAT HIDES SEMANTICS.
`boundary_enumeration_model.spl:195` projects `limit_names: sorted_text_list(names)`
only. A driver reporting `maxImageDimension2D = 1` compares structurally equal
to one reporting `16384`, and the three carefully-sourced values in the fixture
(`boundary_enumeration_provider.spl:133-135`) are never read by any assertion.
The docstring discloses the choice, which keeps it honest, but for a *software*
counterpart on a *fixed* host the magnitudes are deterministic and should be
compared.
**Fix:** compare limit values too when both sides are the same provider, or add
a per-limit floor assertion (`maxImageDimension2D >= 4096`).

### L2-F5 (LOW) — the docstring claims an assertion the file does not contain
**Mode:** 7 MEASUREMENT-TRAP EVIDENCE.
`device_enumeration_boundary_spec.spl:35-37` promises to "prove the framework's
vacuity rule rejects a plan whose only 'comparison' is against an unavailable
source". No `it` block in the file calls any plan-rejection function
(`counterpart_plan_rejections` is not even imported).
**Fix:** delete the sentence or add the scenario.

---

## Lane L3 — readback gate (`vulkan.present.readback_image@1`)

L3 is the strongest of the four and I want to say that plainly. Its four
sabotage scenarios each flip exactly one field off a shared valid baseline and
then assert the gate names *that field* by string
(`readback_boundary_gate_spec.spl:132-219`) — non-tautological, targeted, and
each has an obvious one-line impl change that breaks it (drop the corresponding
clause from `readback_boundary_rejections`). It ran and fully passed:
`.../scratchpad/readback_spec.log` → `Results: 11 total, 11 passed, 0 failed`,
and 11 matches the 11 `it` blocks in the file, so nothing was silently dropped.
The `unavailable` verdict is real, not asserted-against-itself: I confirmed the
marker string is genuinely produced by
`src/os/compositor/vulkan_compositor_backend.spl:162`. Independence grouping is
correct (anv and lavapipe share `mesa`, asserted at `:248-250`). Two findings.

### L3-F1 (MEDIUM) — the "one-pixel image difference" is a one-character change to a made-up label
**Mode:** 6 NORMALIZATION THAT HIDES SEMANTICS / naming misrepresentation.
`readback_boundary_gate_spec.spl:112-113` defines the "image" as the text
`"pixel-hash:8f3a9c2b-64x64-rgba8"`, and `:205-219` diverges it to
`…8f3a9c2c…`. `ReadbackCandidate.candidate_image_bytes` is a `text`
(`boundary_readback_gate.spl:38-40`), so the gate is a string-inequality check.
The gate itself is honest about this ("a caller-chosen stable encoding", `:34`),
but the scenario title claims a pixel-level property the file never exercises,
and the hash value is invented rather than produced by lavapipe.
**Fix:** rename the scenario to "rejects a differing image digest" until a real
lavapipe render supplies the digest.

### L3-F2 (LOW) — lavapipe is described as the counterpart but is never invoked
**Mode:** 5 UNAVAILABLE-AS-PASS (disclosed).
`:25-27` states outright that "nothing here requires it to actually be
invoked", so this is disclosed, not concealed — but the lane therefore has no
executed counterpart and no artifact hash for lavapipe (its manifest at
`boundary_readback_lavapipe_provider.spl` is descriptor data only).
**Fix:** none required for this lane's stated scope; track it as the open step
to a real comparison.

---

## Lane L4 — provider inventory

### L4-F1 (CRITICAL) — the headline sabotage asserts that the fake SUCCEEDS, and calls that "caught"
**Mode:** 4 VACUOUS SABOTAGE.
**Location:** `provider_inventory_spec.spl:189-211`, scenario
*"catches a relabelled lavapipe faking independence from the rest of Mesa"*.
What it actually asserts:

```
assert_equal(provider_inventory_independent_reference_count(honest_selection), 1)
assert_equal(provider_inventory_independent_reference_count(selection), 2)   # the FAKE selection
assert_true(count(selection) != count(honest_selection))
```

`provider_inventory_independent_reference_count`
(`provider_inventory.spl:206-216`) counts distinct `independence_group` strings.
Given a relabelled lavapipe it returns 2 — i.e. **the relabelling worked and the
predicate was fooled**. The spec asserts exactly that outcome and names it a
catch. There is no gate anywhere that detects a mislabelled group; the "catch"
is an author who already knows the honest answer, which is not a test. The plan
doc repeats the framing at
`doc/03_plan/os/vulkan/board_vulkan_parallel_soc_lanes_2026-08-10.md`
("a plan author comparing those counts catches the fake grouping").
**Fix:** make the grouping derivable, not declared — add
`provider_inventory_group_of(provider_id)` keyed on the measured package
(`dpkg -S` of the pinned `.so`) and assert the *declared* group equals the
*derived* one, so a relabel fails.

### L4-F2 (MEDIUM) — "pins real measured identity, never a placeholder" only checks a string prefix
**Mode:** 1 TAUTOLOGICAL ORACLE.
**Location:** `provider_inventory_spec.spl:148-154`:
`assert_true(manifest.artifact_hash.starts_with("sha256:"))` over hard-coded
literals (`provider_inventory.spl:83,95,107,119,131,146,158,175`). The assertion
holds for `"sha256:"` followed by anything, and nothing binds a hash to a file
path — the manifests do not record one. So the hashes silently rot on the next
Mesa package upgrade.
To L4's credit the hashes are genuinely real: I verified three against the host —
`sha256(/usr/bin/glslangValidator) = 96ea85d4…d026`,
`libvulkan_lvp.so = 9d69cae2…c139`, `libvulkan_intel.so = 9ecefd82…22e4` — all
exact matches. The provenance claim is honest; the *oracle* is not.
**Fix:** store the pinned path per provider and compute
`artifact_sha256_of_file(path)` at run time as L1 does
(`boundary_spirv_provider.spl:160-161`), asserting equality with the pinned
literal.

### L4-F3 (MEDIUM) — the sabotage that did turn red used a shared-constant blast, not a targeted flip
**Mode:** 4 VACUOUS SABOTAGE (weak, not vacuous).
`.../scratchpad/l4_run_red.log` → `Results: 10 total, 4 passed, 6 failed`, with
`assert_equal failed: expected mesa, got SABOTAGE_FAKE_GROUP` and
`assert_equal failed: expected 0, got 2`. The sabotage edited
`INDEPENDENCE_GROUP_MESA` itself, so six of ten scenarios failed at once —
including `provider_inventory_rejections`, which is unrelated to grouping. Broad
collateral means the red does not isolate *which* comparison detected the
injected divergence; contrast L3, where each sabotage moves exactly one
assertion. The green baseline is real (`l4_run.log` → `10 total, 10 passed`).
**Fix:** sabotage one provider's group field, not the shared constant, and assert
the specific scenario that flips.

### L4-F4 (LOW) — plan doc cites `Results:` lines that do not exist
**Mode:** 7 MEASUREMENT-TRAP EVIDENCE.
The plan section says "**Sabotage proofs run (see spec for the exact `Results:`
lines)**", but no `Results:` line appears in the spec or the plan — the only
copies are in a scratchpad log that will not survive the session.
**Fix:** paste the two `Results:` lines (green and red) into the plan section.

---

## Shared frame (`soc_profile.spl`, `counterpart_plan.spl`)

### FRAME-F1 (MEDIUM) — two lanes disagree on venus's independence group
**Mode:** 3 FAKE INDEPENDENCE (latent).
`board_vulkan_counterpart_plan_spec.spl:125-127` asserts
`virtio_venus_board_profile().mesa_independence_group == "virglrenderer"`, while
`provider_inventory.spl:139-146` puts `provider_venus_guest()` in `mesa`, and
`boundary_enumeration_provider.spl:35-39` explicitly calls venus-via-Mesa part
of the `mesa` group. Both readings are individually defensible (the guest ICD is
Mesa; the host renderer is virglrenderer), but as *data* they conflict: a
selection mixing `virtio_venus_board_profile` with any Mesa provider will count
2 independent references where the honest answer is 1. This is exactly the
miscount L4 exists to prevent, arriving through a different door.
**Fix:** pick one grouping for the venus guest ICD (`mesa` is correct — it ships
in `mesa-vulkan-drivers`) and record the host transport separately, e.g.
`transport_group: "virglrenderer"`.

The rest of the frame is sound: `board_runnable_count() == 0` is asserted as the
filed gap (`:121-123`), and the two false-claim sabotages (`:186-202`) plus the
self-oracle-only plan rejection (`:204-226`) exercise real predicates with
namable one-line breakages.

---

## Summary

| Lane | Verdict | Real findings | Green verdict acceptable? |
|---|---|---|---|
| L1 — SPIR-V boundary | **VACUOUS (as measured)** | 3 (1 critical, 1 high, 1 medium) | **NO** — spec never executed (parse error, 0 examples run); re-run required |
| L2 — device enumeration | **WEAK** | 5 (2 high, 2 medium, 1 low) | Only as a comparator unit test; **not** as a counterpart boundary |
| L3 — readback gate | **SOUND** | 2 (1 medium, 1 low) | **YES** — 11/11 executed, targeted sabotages, honest `unavailable` |
| L4 — provider inventory | **WEAK** | 4 (1 critical, 2 medium, 1 low) | Inventory data yes (hashes verified real); the independence *sabotage* claim **NO** |
| Shared frame | SOUND with one data conflict | 1 (medium) | Yes |

**Verdicts to reject:** L1's entirely (it has never run), and L4's claim that a
relabelled `independence_group` is "caught" (the spec asserts the opposite).

**Most severe three:**
1. `.../spirv_spec.log:1935` + `boundary_spirv_canonicalize.spl:123` (as of 00:40) —
   L1 executed 0 of 15 examples; every L1 claim, green and red, is unsupported.
2. `provider_inventory_spec.spl:189-211` — the independence sabotage asserts the
   fake succeeded and labels it a catch; nothing detects a relabel.
3. `boundary_spirv_canonicalize.spl:128-163` — DCE deletes `OpLabel` and
   `OpExtInstImport`, so deleting `builder.emit_label()` from
   `boundary_spirv_provider.spl:66` is undetectable by this boundary.
