# Shared mono publication before final verification

The retained route and future archived final factory need the same mono warning,
statistics, diagnostic and E-MONO-033 publication. This change extracts that
existing behavior into `driver_mono_publication_v1` without admitting any caller
body, report, prerequisite hash or final repository.

`driver_publish_mono_warnings_and_stats_v1` publishes ordered warning messages,
prints the unchanged generic/call-site/specialization/unresolved receipt and
logs that output is ready. `driver_publish_mono_diagnostics_v1` publishes every
ordered diagnostic as an error, records the same `monomorphize` pass receipt
with actual profile/module count/diagnostics/errors, and returns false with the
unchanged E-MONO-033 refusal if any error was emitted.

The retained caller still assigns `ctx.hir_modules = mono_modules` between
the helpers. It passes that assigned inventory's count to the diagnostic
publisher. Fatal diagnostics still stop before actual post-mono verification
and its shared E-MONO-031 policy publisher. `CompileContext` is a class, so
the helper calls use its existing warning/error mutation owner.

Extracted bodies differ only in indentation, `self.ctx` becoming the actual
`ctx` argument, and the module count becoming that caller-supplied count. The
new diagnostic helper returns true for the former nonfatal continuation.
Publication is not proof that mono executed: archived factory callers must use
the actual root/FIFO execution statistics and diagnostics, then genuinely
registered immutable verification-use and actual report replay before final
policy admission. No final factory/read placeholder is exported here.

Validation is source-only exact extraction and ordering checks plus working and
staged guards. No native compiler job or execution was run, and this makes no
RSS, reclamation or full-route qualification claim.
