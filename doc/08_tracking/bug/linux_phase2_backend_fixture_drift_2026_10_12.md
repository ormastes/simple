# Linux Phase 2 backend-bound fixture drift

Status: FIXED by focused fixture correction; full native bootstrap remains unqualified. CI38162989607 at51b15dc failed four of16 contract scenarios. Actual diagnostic reproduction proves missing mandatory --backend rejects before verifier and memory validation. Fake verifier also omitted verification_backend in summary and command-owner receipt.

Fix only the test fixture: exercise all14 existing scenarios on both LLVM and Cranelift, enforce backend forwarding, emit backend-bound receipts, and reject missing/invalid backends before verifier work. Production runner unchanged.

Qualification: corrected32 runner scenarios PASS once; shell syntax PASS. No compiler or full bootstrap executed.
