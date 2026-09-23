# Dynamic backend loader real-execution verification

Status: **HOLD**

- Authoritative TODO: `todo_db.sdn` row 106, OPEN P2.
- Structural baseline: RED because the old spec remained source-text pinned.
- Structural candidate: PASS.
- Real fixture build: PASS with pinned LLVM 23.1.1 `clang-cl.exe`.
- Bootstrap-seed behavioral run: 4/5 PASS, then exposed that `DynLib.sym_checked`
  raises on a normal missing-symbol result after checked out-parameter writeback
  is lost.
- The candidate routes symbol probing through the existing nonfatal host dynlib
  owner and closes the library and private stage on a miss.
- The final unrerun candidate also binds the admitted lease build ID and staged
  path to the selected bytes, uses process-unique fixture directories, and
  requires a C unload marker after close. The post-load digest branch retains a
  structural guard; a constructor-driven mutation negative control remains
  pending.
- The three-cycle cap was reached before that repair could be rerun. No
  self-hosted acceptance claim is made and the TODO row stays OPEN.
