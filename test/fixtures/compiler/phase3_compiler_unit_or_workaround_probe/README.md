# Compiler owner qualification workaround probe

Status: **UNEXECUTED**. Temporary workaround P3-OR-18; no permanent compiler fix or admission claim.

Imports the actual six compiler enum declarations used by the twelve modified compiler files. The executable checks every listed unit arm and a nonmember for SymbolKind, MirBinOp, HirBinOp, MirTypeKind, DimCheckTiming, and HirTypeKind. Expected stdout lines: `1,1,1,1,0,2,2,0,3,3,0,4,4,4,0,5,5,0,6,6,0`.

This import closure may encounter independent HIR, monomorphization, MIR or object failures. Preserve those diagnostics. An object is not runtime PASS; linking/running compiler-owner imports requires generated entry/module initializer coverage, not the old Hello entry.

Actual production scope includes mixed HirTypeKind `Named(_, _) | Any | Error` and `Error | Optional(_)` arms. Their payload alternatives are unchanged; the full compile of the affected source files is the direct regression gate. Genuine differing-payload binding rejection remains required and is provided by the companion plugin fixture suite.
