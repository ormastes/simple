# Module resolution agrees with the Lean path model

Status: **AUTHORED_UNRUN**. This is a manual scenario projection of
`test/01_unit/compiler/dependency/resolution_spec.spl`; neither the spec runner
nor doc generation has executed for this change. It records no PASS counts.

Owner: `src/compiler/00.common/dependency/resolution.spl`.
Reference: `src/verification/module_resolution/src/ModuleResolution.lean`,
`toFilePath`, `toDirPath`, and `resolve`.
Trace: `REQ-SSPEC-COMPILER`.

All filesystem inputs below are literal `FileSystem.files` values. They are
independent of the path builders being tested. The outcome assertions inspect
the actual resolver's enum kind and payloads through a formatting-only helper.

| Scenario | Owner operation and expected observation |
| --- | --- |
| Read the Segment name field | `Segment(name: "alpha").name` is `alpha`. |
| Build both nested module path forms | Segments `alpha`, `beta` under `src` produce `src/alpha/beta.spl` and `src/alpha/beta/__init__.spl`. |
| Resolve a file-only filesystem | Only `src/alpha/beta.spl` exists: `Unique(File, "src/alpha/beta.spl")`. |
| Resolve an initializer-only filesystem | Only `src/alpha/beta/__init__.spl` exists: `Unique(Directory, "src/alpha/beta/__init__.spl")`. |
| Resolve a filesystem containing both module forms | Both literal paths exist: `Ambiguous` contains the file path first and initializer path second. |
| Resolve a filesystem containing neither valid module form | Only the bare path, former `__init__.spl.spl` path, and an unrelated file exist: `NotFound`. |

Six active cases are authored. The historical commented migration catalog in
the spec remains preserved and contributes no cases or verification evidence.
The separate physical-filesystem native fixture is outside this unit manual's
scope; its result must be reported independently.
