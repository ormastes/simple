# Collect only receipts for the admitted immutable task

Authored manual; generated-doc verification is pending a usable source-matched
runtime. These scenarios use local receipt/output files and launch no compiler.

1. Write correctly hashed output and a receipt whose task name, attempt and
   host match but immutable digest differs. Collection must reject it.
2. Remove the output while retaining that stale receipt. Collection must still
   report the identity mismatch, before attempting output inspection.
3. Write a failed stale receipt with no output entries. Collection must reject
   it even though there are no files to hash.
4. Write matching identity and correctly hashed output. Collection must return
   that receipt and preserve the output digest.

The rejection guard also precedes remote output transfer in the implementation;
these local scenarios do not claim live SSH transfer evidence.
