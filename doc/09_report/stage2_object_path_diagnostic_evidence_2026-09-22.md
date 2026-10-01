# Stage 2 object-path diagnostic audit, 2026-09-22

STATUS: WARN — production repair already merged; native wrapper A/B still pending.

Scope: `bootstrap_stage2_backend_object_path_status_2026_09_08`, isolated
`D:/wk-p1-stage2-object-path`, base `e0dd873da1b`. No compiler or runtime code
was changed. Existing unrelated dirty files in the primary checkout were not
used as authoritative sources.

## Existing fixes and actual pending criterion

- [PR #1072](https://github.com/ormastes/simple/pull/1072), merge
  `585b5799baed2292b294fb6b26391b3a63f6e909`, repairs the reader's nullable
  transport. Its native A/B was explicitly unverified; the clean DB already
  says `fix-implemented-verification-pending`.
- [PR #748](https://github.com/ormastes/simple/pull/748) fixes stale object
  publication and reports Linux AArch64 sanity success. This is historical
  evidence, not a fresh Linux run.
- [PR #940](https://github.com/ormastes/simple/pull/940) fixes Windows object
  publication through a long-path-safe rename. This audit adds no rename fix.

To close the remaining criterion, the native old-wrapper/new-wrapper
differential must execute the real public reader, preserving exact diagnostic
bytes and rejecting missing/oversized inputs. Current driver diagnostic
recovery alone does not prove that differential because the driver also has
a raw-reader fallback.

## Artifact binding

Used the pure-Simple admitted Stage 2 candidate at
`D:/wk-stage2-llvm-c-link/.simple/storage/build/bootstrap/stage2/x86_64-pc-windows-msvc/simple.exe`,
SHA-256 `be0ad06d6a68b466785eae2c1cb966f61c7026dd5fae8242591353760d72c7c2`.
The sibling `stage3/x86_64-pc-windows-msvc/stage2-admitted/admission.env`
has status `admitted`. Source, runtime, tool and sanity snapshot hashes were
checked against its fields; the admission hash also matches the parent
provenance receipt. This compiler predates this audit; it is not a rebuild of
every source on current main.

The following exact owner hashes match both admitted source inventory and
current clean main:

| Owner | SHA-256 |
|---|---|
| `src/lib/nogc_sync_mut/io/file_ops.spl` | `667abc41f008d9388243e3fbaf0377542614258438f400e1886b854ca38b8fcb` |
| `src/compiler/80.driver/driver_aot_native_output.spl` | `8561acaee7e2a5b026bc23614ee4a83cb342f53cf4dd0ff607792b445609af61` |

## Native observations and controls

All compile attempts used the candidate above, LLVM 23.1.1, its frozen
`--runtime-path`, `--backend=llvm`, isolated cache paths, and
`SIMPLE_NO_STUB_FALLBACK=1`. Native Windows/MSVC environment keys were folded
to uppercase before adding PATH: duplicate `Path`/`PATH` initially selected
the wrong LLVM DLL and exited `0xC0000139` before main. That setup failure is
not evidence about the language defect.

| Check | Exit/result | Elapsed seconds | Sampled peak tree RSS bytes |
|---|---|---:|---:|
| Candidate version baseline | 0, `simple-bootstrap 1.0.0-beta.14` | 0.281 | 18,399,232 |
| Existing whole-module diagnostic-reader probe native build | `0xC0000005`, after HIR | 18.656 | 761,593,856 |
| Extracted reader/path capsule compile | 1, concrete LLVM error recovered | 22.843 | 119,611,392 |
| Existing hello-world native build | 0, executable produced | 83.531 | 263,426,048 |
| Hello executable | 0, exact stdout `hello` | 0.125 | 4,448,256 |

The capsule is a diagnostic-recovery characterization only: it extracts
production function bodies but flattens module context, and its manually
declared `rt_platform_name` nullable signature differs from the source owner.
It was rejected by LLVM for a duplicate `_host_windows_flag` global and never
executed. It therefore supplies an actual failing-provider input to the
already compiled native driver's diagnostic path, not wrapper semantics proof.
The driver surfaced the concrete provider reason:

```text
AOT compile error in ...: llc failed (exit 1):
... error: redefinition of global '@g_...___host_windows_flag'
```

The retained-log checker rejects five mutations: zero exit, timeout, excessive
RSS, removal of the concrete LLVM error, and an appended opaque object-path
status. These are evidence-checker negative controls, not native wrapper
mutation tests. Checker scope is explicitly limited to diagnostic recovery.

Metrics sample the sum of live process-tree working sets every 50 ms using
psutil. They are lower bounds on true peak RSS; short child spikes may be
missed. No production change was made, so these are characterization and a
local baseline, not a claimed before/after performance improvement. The earlier
artifact's retained hello sanity receipt was 23.468 s; this run's 83.531 s is
slower under different cache/environment/concurrent-load conditions and needs
a controlled comparison before attributing a compiler regression. No repeated
passing run was made. The three native compile attempts exhausted this scope.

## Reproduction and retained evidence

Existing integration source:
`test/02_integration/bootstrap/probe_stage2_object_path_diagnostic_read.spl`.
Its native compile command was:

```text
<admitted-stage2> native-build test/02_integration/bootstrap/probe_stage2_object_path_diagnostic_read.spl --backend=llvm --runtime-path <frozen-stage2-runtime-authority> -o build/object-path-evidence/probe.exe
```

The retained local directory `D:/wk-p1-stage2-object-path/build/object-path-evidence`
contains `run_probe.py`, `capsule.py`, `diagnostic_capsule.spl`, `hello.py`,
per-attempt logs and JSON metrics. These local build artifacts are not shipped
with the patch. The failing-provider log SHA-256 is
`4653a7fe7af94659c7135c92c5562aa8b46e41736343807916ac3b4a3d74bf40`.

Validate the retained recovery evidence and five negative controls:

```text
sh scripts/check/check-stage2-object-path-diagnostic-evidence.shs --evidence build/object-path-evidence --admission D:/wk-stage2-llvm-c-link/.simple/storage/build/bootstrap/stage3/x86_64-pc-windows-msvc/stage2-admitted/admission.env
```

Windows x86_64/LLVM is the only fresh execution claim. Windows long and mixed
paths, non-Windows host semantics, AArch64, other CPUs, and other backends remain
unverified here. In particular, POSIX backslashes must remain filename bytes;
no path normalization changes were made. Native missing-file controls were not
reached because the whole-module executable was not produced. Keep the DB
pending and the remaining full-wrapper integration gap visible.
