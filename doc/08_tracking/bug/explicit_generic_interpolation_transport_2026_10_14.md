# Explicit generic arguments lost in canonical compiler interpolation

Status: CLOSED 2026-11-03 (not reproducible; premise unproved). The six typed helper calls are no longer inside interpolation: function_field_call.spl (f9487416d09, 49daf595b38) uses concrete non-generic _function_field_*_enum_discriminant helpers, and mono is removed (erased generics), so E-MONO-033 cannot arise from erased explicit args. The report itself established no general interpolation failure (local and imported fixtures retain explicit args). Reopen with a fresh stage3 repro if it recurs.

Current release_phase3 source contains six explicitly typed generic helper calls inside function_field_call.spl diagnostic interpolation. Actual producer a713, source8b4cc355, canonical381-module closure records six flat_count=0/rich_count=0/HIR_count=0 calls before monomorphization. Four calls infer their arguments; two refuse specialization with E-MONO-033. Local six-call and imported two-module native fixtures retain explicit arguments and pass, so a general interpolation/import/impl failure is not established.

Compatibility workaround: evaluate the same six explicitly typed helper calls once in their existing profile-receipt branch, then interpolate their i64 results. Output text, argument order, branch conditions and capability bridge remain unchanged. No generic, identity, payload or publication guard is disabled. This is a recorded workaround, not a parser repair or a completed bug mark.

Native canonical verification is pending for this workaround. Original canonical failure, flat/rich/HIR traces, local contrasting fixtures and owned GDB observation failure remain preserved under build/review/item5-functionfield-trace-object-20261013 and related evidence. Full Phase3 compilation plus produced-compiler Hello remain required before landing.

**Revalidated 2026-11-02: still plausible because OPEN. Root cause before rich AST bridge remains unproved; no merged fix commit with a passing regression is cited in this doc.**
