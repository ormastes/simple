# Legacy containment query loses Go delimiter braces

Status: source-confirmed defect; isolated source correction and regressions
AUTHORED_NOT_RUN. No compiler, seed, Podman or native campaign ran. Observed
release: `269ec58d0c1c3c3b83f9653ac191f324347686c2`.

`src/lib/nogc_async_mut/container/providers/linux/containment_inspect_v1.spl:17`
used ordinary-string double source braces for all Go template actions. Simple's
`decode_interpolation_brace_escapes` in
`src/compiler/10.frontend/core/string_interpolation_expand.spl:154` rewrites each
doubled opening/closing brace to one. The existing language spec
`test/01_unit/language/string_brace_escape_collapse_spec.spl` documents ordinary
`{{` becoming `{` and raw text preserving braces. Consequently the intended Go
`{{json .Id}}` reaches the engine as a single-brace literal. The same defect
affects all twenty-two actions, including nested security-option range/if/end
blocks and the final JSON object close.

The exact public legacy call chain is
`LinuxSimpleContainerAdapterV2.capture_containment_v1` at adapter line164 through
`LinuxOciRuntimeProviderV1.capture_containment_v1` at runtime line536 to this
builder at line559. The runtime first checks the request, installed containment
profile, scope, retained identity and current provider pins. It uses the same
command for both the pre-query (line562) and post-query (line586). The first
strict nineteen-field JSON parse occurs at line566, before a native association
can be published. The post-query repeats parsing and PID/cgroup checks.

Thus this is reachable through a configured public legacy adapter/provider
capture, with the required real profile/retained workload. The malformed literal
response fails closed at query/rendering or strict JSON parsing; it does not
silently grant containment. Bounded direct-reference inspection found no common
facade dispatcher for this legacy method. No claim is made that an installed
native runtime was available or that all container launches use this path.
The new fresh fixed42 query and frozen query6 extraction are separate and are
not edited by this correction.

The correction quadruples source action braces in this one ordinary literal,
so runtime Go action delimiters remain doubled. Its intended fields, values,
native-ID validation, typed argv, parser and capability/security/identity checks
are unchanged. No shell, executor, admission or native export is added.

The prior two substring checks also used ordinary doubled source braces. They
could match the same malformed single-brace output, and were not a sound
regression oracle. They are replaced with equality against a full independent
raw-string expected native template. A separate prevention case checks all
twenty-two action delimiter pairs, nested range/if/end bytes and the third final
JSON closing brace. Existing payload refusal cases remain intact.

Expected source behavior: the new full-template assertion detects the old
literal and the corrected literal retains the intended Go bytes. This prediction
is backed by the compiler source; no failed-before or passed-after execution is
claimed. All five source scenarios remain NOT_RUN. Actual Podman template/schema
and native containment qualification still require their own permitted fixture.

Correction accounting: prior input producer one source-only correction; query
extraction zero; this separate template defect one correction. The existing
six-cycle qualification cap is unchanged, with zero additional compiler/native
cycles. Independent Astra source review is required before landing.
