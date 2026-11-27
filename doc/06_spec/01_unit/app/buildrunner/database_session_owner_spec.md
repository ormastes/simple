# Preserve the imported session owner

Authored manual; generation awaits a qualified SSpec runtime.

1. Open the imported `Result<SessionProbe?, text>` and extract its present
   session with an explicit receiver type.
2. Call finish before settlement. Require the actual error message, proving
   an incomplete session cannot report success.
3. Settle the same session. Finish must now return 42, which depends on the
   preceding mutation to 41.

The paired native mains provide separate compiler evidence: the unannotated
probe fails MIR; the typed variant builds and actually prints 42 with exit 0.
They do not qualify a production manager or strict process provider. The bug
record retains exact artifacts and unresolved qualification states.
