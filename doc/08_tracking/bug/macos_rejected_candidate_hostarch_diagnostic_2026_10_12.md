# Rejected macOS candidate host-query diagnostic

Diagnostic only; native execution UNEXECUTED and compiler UNADMITTED. Existing run38161323992 artifact11712181880 preserves Mach-O arm64 simple.rejected42988928bytes SHA4040420a1d187b9c3e011be92565387b04d319a4f2f5df432d65ab94836ecf81. Source frozen5e022fd. No compiler rebuild or architectural fallback.

Actual binary shell_output uses rt_tuple_get indices0/1/2 then rt_value_unbox_int. Verified instruction return checkpoints +0x70 stdout,+0x80 stderr,+0x90 unboxedcode. Raw io helper passes raw command pointer,length,args to actual Rust rt_process_run; command text getter inspection is gated by actual host_arch then shell_output. String getters rt_string_len/data use frozen reprtransparent RuntimeValue and validate type. Diagnostic getter calls are bounded; invalid values or unresolved symbols refuse COMPLETE. Capture posttrim and actual host_arch return; all receipts explicitlyUNADMITTED. External timeout120/kill10 bounds entire debugger; missinghost breakpoint, childescape, entitlementdenial, getterfailure, missingartifact or toolauthority isFAIL, notPASS.

Local verification: recoveredSHA and instruction offsets reviewed, Python AST parsed. Native LLDB callbacks are unexecuted; no native behavioralPASS claimed. Windows/Linux/BSD/SimpleOS source behavior is untouched.
