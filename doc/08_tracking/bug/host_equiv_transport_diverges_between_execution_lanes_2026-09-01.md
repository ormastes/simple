# `host_equiv_transport_check` passes on the JIT lane and FAILS on the interpreter

**Date:** 2026-09-01
**Found by:** the pre-commit audit; **reproduced by the parent.**
**Status:** OPEN. Does not block the firmware work, but the "one source, two
substrates" claim is weaker than stated until this is understood.

## Measured

```
default (cranelift JIT):  108 PASS / 4 FAIL  -> HOST EQUIV TRANSPORT OK
SIMPLE_EXECUTION_MODE=interpret:
                          107 PASS / 5 FAIL  -> HOST EQUIV TRANSPORT FAIL (1)
```

The extra failure, reproduced twice, at
`examples/09_embedded/simpleos_nvme_fw/fw/host_equiv_transport_check.spl:108`:

```
FAIL: genuine CQE carries the real read payload -- expected 90 got 0
```

(The 4 shared FAILs are the deliberately-unbound `board:` profile and are
expected on both lanes.)

## Why it matters

Two readings, and **which one is true is NOT established**:

1. The default-lane pass **leans on JIT behaviour** — plausibly the interior-collection
   aliasing of [[struct_nested_array_assign_aliases_not_cow_2026-09-01]], where a
   payload survives because a copy silently aliased rather than because the
   transport carried it. If so, the assertion is passing for the wrong reason and
   the read path is weaker than the check claims.
2. The **interpreter drops the payload** — a second, independent lane defect.

Reading 1 would mean a green that certifies nothing. Reading 2 would mean the
interpreter, currently the recommended mitigation for the COW defect, is itself
unsound on this path. Both are worth knowing; neither is assumed here.

## Related, and part of the same picture

6 of the 14 firmware checks print `[engine-demotion] reason=hybrid-interp-splice`
**even on the default lane**, so "the default lane" is not a single engine. Any
lane-comparison must record which engine actually executed — see
[[execution_lane_silently_demotes_green_result_is_not_evidence_2026-09-01]].

## Reproduce

```sh
cd <repo root>   # NOT the example dir
SIMPLE_EXECUTION_MODE=interpret SIMPLE_TIMEOUT_SECONDS=0 \
  bin/simple run examples/09_embedded/simpleos_nvme_fw/fw/host_equiv_transport_check.spl
```

## Next step

Determine which reading holds before trusting either lane on this path: instrument
the CQE payload write/read on both lanes, or bisect the assertion to the first
point where the two diverge. Do **not** "fix" it by relaxing the assertion —
the assertion is correct in both readings; one of the lanes is wrong.

## Scope

Interpret-lane parity is **confirmed** for `nvme_registers_check`,
`admin_transport_check` and `nvme_ready_gate_check`. The other 10 checks were
still running at audit cutoff (interpret is ~10x slower) and are **unverified on
that lane** — not known good.
