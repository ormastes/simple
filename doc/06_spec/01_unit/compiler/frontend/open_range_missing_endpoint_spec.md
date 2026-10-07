# Missing Range endpoints in the flat frontend

Executable: `test/01_unit/compiler/frontend/open_range_missing_endpoint_spec.spl`.

| Scenario | Actual contract |
|---|---|
| Parenthesized open end | Flat Range right child is absent node ID -1; converted tree endpoint is nil. |
| Authored negative endpoint | A source bound of (-1) retains a nonnegative node ID and a present tree endpoint. |
| Bounded positive endpoint | The right child remains integer literal 4. |
| For-body delimiter | `1..:` leaves colon outside the Range and preserves absence. |
| Named call-argument continuation | `f(start..)` retains an absent endpoint through parse_binary_from. |

Phase1 evidence uses immutable bootstrap seed SHA57aeb8786f2a767b2052672b988b6bcfcabff2a3033594e97606ceabc7ebb3ce. Baseline original three cases: two pass, open-end case fails. After repair only the original failed case reran (one pass); two new grammar cases ran separately (two pass). Combined case coverage is five; this is not a fresh full-file five-case run or self-hosted native admission.

Independent native failure remains the required integration regression: producer SHAcd000950b565769d8261d03d0fe822c712e28212bf67d8dc6d3c31bb19da0327 built the original open_range_break fixture, whose linked output printed0 instead of6. Rebuilding the pure frontend with this repair and compiling/running that unchanged fixture must print6. Compiler compile exit139 at LLVM shutdown remains independently blocking until repaired; artifact execution cannot erase that failure.
