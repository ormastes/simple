# Record-returning capturing callback rejected by native lowering

Status: reproduced; repair and behavioral verification pending.

Admitted pure-Simple producer: 4c479a0d3f25bcb73a9c4c8fe1735b7743c65862076c73e079b7f7bc9c607036, source f7e315569. Exact runtime capsule selected and SIMPLE_NO_BOOTSTRAP_DELEGATE=1. Probe: test/02_integration/compiler/backend/probe_struct_field_fn_call.spl; corrected input digest 0ec089b5b14d0977a25578f8406a98e6fc9f3dbf9252934b35c8f8dfbb627b4e.

The authored fixture initially escaped lambda backslashes as if inside a string. Corrected to actual language syntax. Parsing then succeeds, but native MIR rejects its execute_fn capturing lambda returning CallbackResult: E-MIR-EXPR-Lambda, closure conversion has not run, line 47 column 21. No native artifact or callback execution was produced. Retained log: /mnt/c/Temp/dbc-callback-corrected-native-probe-20261012.log.

Required outcome stays unchanged: a typed array loop invokes the actual callback, preserves the captured offset, and reads the returned record value and label. Do not replace this scenario with constant callbacks, reinterpret the return as an integer, or weaken the assertion to mere compilation.
