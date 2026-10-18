# Genuine Value owner constructor compatibility

Source: `test/01_unit/compiler/value_owner_constructor_spec.spl`.
Shared controls: `test/01_unit/compiler/value_owner_constructor_native.spl`.

Status: **UNRUN**. This manual describes executable assertions, not accepted
runtime evidence. The BDD wrapper and explicit native entry call the same four
real helpers; no mirrored implementation or placeholder pass is used.

| Case | Real assertion |
|---|---|
| Primitive payloads | Genuine Value Bool/Int/Float/String payloads, signed limits, empty/Unicode strings; real SdnValueKind collision owner remains visible. |
| Collections | Actual array/tuple/dictionary/struct payload order, keys and values; inputs retain original values. |
| Record carriers | Function symbol/name, closure parameters/captures/body kind and payload, declared type kind/width/sign, complete source and type spans, object class/handle and opaque scalar carrier. |
| Optional payloads | Actual owner Option/Result factories preserve Some/nil placement, wrapped Value and original inputs. |

Function/object handles and opaque payloads are carrier tests only. They do not
prove callability, object-store membership or foreign pointer dereference.

A future native PASS qualifies the source workaround on the old producer only.
It does not qualify a newly implemented lowering engine or the full interpreter.
Canonical compilation of all four actual interpreter consumers remains required.
This shares the existing constructor feature's three-cycle limit; the prior
engine attempt failed and the new native controls have not run.
