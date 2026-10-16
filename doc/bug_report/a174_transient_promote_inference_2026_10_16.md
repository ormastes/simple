# Retained producer fails generic transient promotion inference

Status: provisional input workaround, executable verification pending; bug DB reconciliation pending qualified tooling.

Full Phase3 cycle3 exited1 after successful15-worker HIR collection. Native monomorphization reported86 generic functions,991 call sites,265 specializations and14 unresolved sites, then E-MONO-033. No MIR/object/link success. Full stderr is preserved externally in phase3-a174-03d33d49-cli-bootstrap-cycle3/tmp/native-build-stderr-11356-1.log.

The parent diagnostic includes transient_promote inference failures with older snapshot paths. Those paths must not be represented as current-source attribution without checking source/cache span provenance. Current matching sites promote text digests and schedules from declared text-returning helpers. Explicit transient_promote<text> arguments preserve values, checked promotion results, pause/end ordering and failure behavior. They avoid asking the retained producer to infer these known argument types. Other Result-valued promotion sites remain under review; this patch does not claim all14 calls repaired.

Affected producer SHA256: a174b8e70b0a0ea4531db2ac5b8553f216590a7fbad0567cd9e40fd8e4630994. Original source and intended-code recovery reference:03d33d497ac6d1408683493f74ff9db434e4cfa3. Current source owner fix and actual post-patch native qualification remain pending. The three full-build attempts are exhausted; no fourth full attempt is authorized by renaming this issue.

Follow-up source review: four Result-valued promotion sites now explicitly use
Result<MonoArchiveFactsV1, text>, Result<bool, text> (two sites), and
Result<MonoArchiveFinalRepositoryV1?, text>. Each type was checked against the
called helper declaration. Added the concrete MonoArchiveFactsV1 import.
Scope begin/pause/end, checked boolean result, diagnostic ownership and error
branches are unchanged. Whitespace validation passed; no executable test or
full retry was run. Prior text workaround commit: b1f6af5b9ea.
