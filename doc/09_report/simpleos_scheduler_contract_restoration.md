# SimpleOS scheduler contract restoration

Date: 2026-09-14. Scope: canonical task state, TCB security/isolation records,
task-constructor initialization, and the Scheduler authority facade.

Historical evidence: commit `43134409de1` introduced `PreparingExit` and the
stable external state code 4. Merge `e274cd33719` removed the canonical enum
declaration while surviving admission/diagnostic owners still referenced it.
The current `simple_os_enhance` requirements, architecture, design, execution
context adapter, and authority runtime require persistent TCB security, but
the referenced `TaskSecurity`/`TaskSecurityBinding` declarations and Scheduler
authority methods were absent in this branch.

The repair restores these source contracts without inferring authority from a
task ID, role, task name, default CSpace, or bootstrap flag. All creation owners
initialize denied security explicitly. A real nonzero lifecycle generation is
required before binding or root admission; old ID-only constructors now use
the paired identity allocator. Fork retains restrictions and omits root/reaper
objects. Filesystem fields default to denied/unbound and survive resource or
domain updates. PreparingExit is terminal for new authority use.

The focused executable spec and authored manual cover default denial, exact
binding, authority grants, state codes/admission, and inheritance. No Simple
build, interpreter, native, SPipe, docgen, or guest test was run: no matching
admission receipt exists for an available self-hosted runner. No Rust seed or
full bootstrap was used. Thread/build work is therefore zero.

Semantic execution: **MissingEvidence**. Production verification is not PASS.
The managed-child launch seam and exit-finalization owners are separate
coordinated repairs; this commit alone does not prove PID1 or guest startup.

Completed static checks:

- Bounded source audit: all nine TCB constructors explicitly initialize
  `security` and `lifecycle_generation`; all referenced security fields have
  declarations; all fifteen authority runtime operations have Scheduler
  methods; the obsolete bootstrap syscall bypass is absent.
- New source/spec scan: no placeholder pass or vacuous boolean assertion.
- `direct-env-runtime-guard.shs --working`: PASS.
- `numbered-artifact-guard.shs --working`: PASS, zero numbered artifacts.
- `find doc/06_spec -name '*_spec.spl' | wc -l`: 0.

These checks establish source consistency only. They do not supply branch
coverage, type checking, native execution, or generated-manual evidence.
