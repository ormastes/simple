# Native Optional array pattern binder loses array type

Status: open; source compatibility workaround authored, runtime UNRUN.

Actual native_noop_admission failure canonical-batch81/unit2 reports native issue143: for-in source MIR type I64 at compiler/80.driver/driver_build/incremental.spl1035. SdnValue.as_array is declared [SdnValue]? (common/sdn/value.spl135). Its result is bound by `if val entries_array=arr`; iterating that bound value is rejected as scalar.

The optional-array pattern binding must retain the array and element types. Negative scalar iterator diagnostics remain required. Related nested array iteration failures are not assumed to have the same exact lowering owner.

Compatibility workaround: explicitly type the bound entries/dependencies/outputs arrays as [SdnValue] inside their existing present branches, preserving missing/wrong-type behavior, order and all cache identity checks. No cast or Any. Removal condition: a rebuilt pure-Simple producer compiles and runs the equivalent unannotated if-val iteration and actual BuildCache.load/native_noop entry without issue143; remove annotation workarounds and rerun real cache load caller checks.
