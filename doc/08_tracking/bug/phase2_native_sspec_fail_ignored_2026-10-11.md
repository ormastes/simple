# Native Phase2 SSpec fail-only branches do not reject cases

Status: OPEN. Independently reproduced; root cause not established.

A pure-Simple native capsule constructed by the user-authorized Rust bootstrap seed reports both `fail("direct sentinel must reject")` and a helper calling `fail(...)` as passing. An unequal built-in matcher in the same capsule fails correctly. Actual output: **3 examples, 1 failures**, although all three deliberately reject. The process also exits zero, the separately recorded SSpec exit-status defect.

Evidence: `build/native_probe/traceability-sspec-fail-control-20261011/main.spl` and `run.log`. Immutable constructor inputs and producer hash are retained beside them. No admitted general-tool or release-runtime claim.

The initial quote/overflow component capsules falsely reported passing because their accepted-input branch only called `fail(...)`. A separate parser probe showed accepted malformed input and saturated overflow; those two PASS results are INVALIDATED. Replacing those rejection oracles with computed `rejected` flags asserted using built-in matchers produced actual RED (2 and 3 failed cases), followed by GREEN after the scalar repairs (3 and 4 cases).

Required follow-up: repair the native failure path and add direct/helper rejection controls before general SSpec or generated-manual qualification. Under this development lane, fail-only branches cannot provide evidence; typed rejection/presence conditions require independently observed built-in assertions. This is an explicit temporary oracle restriction, not an accepted language workaround or full test-runner qualification.
