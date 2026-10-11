# Tagged explicit global-pool type argument workaround

Tag: TEMPORARY_WORKAROUND_EXPLICIT_GLOBAL_POOL_TYPEARGS. Runtime qualification remains incomplete.

`original.spl` is the exact nine global declarations/helper/calls extracted from source a0e3 and remains UNEXECUTED as a standalone fixture. Real imported-compiler object compilation already demonstrated nine E-MONO-032 errors at the original call sites; full Phase3 stopped earlier at its eighteen HIR failures.

`local_typeargs_control.spl` is byte-identical to the actual aa404 control: compile exit0, three generic specializations, link exit0, runtime SIGSEGV(-11), empty stdout/stderr. It proves grammar and object generation only; it does not qualify runtime transport. Receipt: `/mnt/c/Temp/simple-explicit-pool-typeargs-control-evidence-20261010/validation/explicit_nested_pool_typeargs/evidence.json`.

The production workaround supplies T as the exact global pool's declared type because the root expression is `[pool]`. It changes no validators or runtime. Permanent declared-global inference repair remains separate. Execute the tagged real source through mono, MIR and object generation with aa404 and normal caches; do not claim full compiler readiness from this fixture.
