import MemoryModelDRF

def main : IO Unit := do
  IO.println "Memory Model DRF Verification"
  IO.println "=============================="
  IO.println ""
  IO.println "This module provides formal verification of the SC-DRF"
  IO.println "(Sequential Consistency for Data-Race-Free) property."
  IO.println ""
  IO.println "Key theorems:"
  IO.println "  - scDRF: Data-race-free programs have sequential consistency"
  IO.println "  - graphCorrectness: HappensBeforeGraph correctly implements happens-before"
  IO.println "  - raceDetectionCorrectness: detectRace correctly identifies data races"
  IO.println "  - runtimeCheckSound: Runtime race detection is sound"
  IO.println ""
  IO.println "See src/MemoryModelDRF.lean for full formalization."
