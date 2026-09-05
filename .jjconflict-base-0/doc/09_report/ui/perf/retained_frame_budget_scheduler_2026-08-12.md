# Retained-frame budget scheduler — 2026-08-12

Status: mechanism/correctness PASS; production consumer wiring remains open.

## Result

`common.ui.render_opt.retained_frame_schedule` combines retained-state validity,
the canonical exact `DamageFramePlan`, and measured p95 budget admission into
one backend-neutral decision shared by Web, GUI, WM, CPU, and Vulkan:

- idle: retain the framebuffer and execute nothing;
- execute: replay the exact admitted plan now;
- reject state: malformed/unseeded retained state must not present;
- defer budget: state is correct but the measured 12.5 ms allowance is exceeded;
- reject profile: missing or invalid performance evidence fails closed.

The receipt is deliberately flat. An initial nested-receipt representation hit
the test worker's 120-second budget twice; flattening plan mode/rects and budget
counters produced a passing focused run and avoids repeated aggregate copies at
the producer/executor boundary.

Focused interpreter spec: 3/3 PASS on the third and final verify/fix cycle.
It covers admitted 109-row mixed-alpha damage, deferred 110-row damage, idle,
malformed state, and invalid profile. O3 analysis completed with five low-level
MIR opportunities and no source-pattern findings.

## Limitation

This scheduler does not silently discard deferred frames; the production owner
must choose coalescing, a lower-cost operation path, or a later frame and record
that decision. Web/GUI/WM adapters are not yet all wired to this receipt, and no
end-to-end 8K p50/p95 or presentation claim follows from this mechanism alone.
