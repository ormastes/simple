# Native comparison confused raw integers with inline floats

The qualified Phase2 compiler `b0fccf9f6667808acbb01bee6dbeaa53f3d0038e31068f9aeee58a21c6b4a53e`
compiled Hello but failed a 13-file import closure with empty declaration tags.
Diagnostic `module_decl_at` calls returned -1 for both indices of a two-declaration
module, and for indices above zero in a 98-declaration module. Disassembly showed
raw index/count operands passed to `rt_native_cmp` for the bounds comparison.

The C comparator accepted the low-bit inline-float tag as float provenance. Raw 2
decoded as floating zero and raw 98 as a tiny subnormal: the original linked
runtime returned `cmp(0,2)=0` and `cmp(1,98)=1`, both incorrect for raw integers.
This is independent of the producer lowering's overly broad dynamic-comparison
selection, which is tracked and repaired separately.

## Repair and contract

Only `rt_native_cmp` float dispatch now requires registered heap-float membership,
matching the existing ordered-key boundary's treatment of raw integer words.
String dispatch and signed integer fallback are unchanged. A separate, pending Simple twin uses
the existing `float_is_valid` and `rt_value_as_float` owners, with confined unsafe
wrappers; it does not introduce a second registry.

Global legacy-inline-float recognition and typed float decoding remain unchanged.
Float allocation/registration failure can still return a legacy inline float;
such a value is deliberately a raw word at this ambiguous comparison boundary.
Without type provenance it cannot be distinguished from ordinary integers with
the same bits. Typed decoding continues to support it. This repair does not claim
new NaN ordering semantics or broaden the raw/boxed ABI.

## Verification

On WSL Ubuntu, Clang compiled the real `runtime_native.c` with
`src/runtime/test/rt_native_cmp_raw_i64_selfcheck.c`:

```sh
clang -std=gnu11 -O1 -ffunction-sections -fdata-sections \
  -DSIMPLE_CORE_C_STANDALONE=1 -Isrc/runtime \
  src/runtime/test/rt_native_cmp_raw_i64_selfcheck.c \
  src/runtime/runtime_native.c -Wl,--gc-sections -lpthread -ldl -lm \
  -o /var/tmp/item5-native-cmp-raw-selfcheck
/var/tmp/item5-native-cmp-raw-selfcheck
```

Actual executable exit 0: **2025 raw comparisons**, real heap string ordering,
registered heap float ordering including mixed raw operands and signed zero, and
legacy typed decode all passed. Compile log:
`/var/tmp/item5-native-cmp-compile.log`. Raw values include all low tags, negative
values, the observed counts 2/72/98, and signed 64-bit extremes.

The Simple twin has not yet been executed. The repaired Phase2 producer and its
dependent import/application qualification are running separately; this focused
runtime result does not claim those applications passed.
