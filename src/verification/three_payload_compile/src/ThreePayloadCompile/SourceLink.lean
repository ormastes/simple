namespace ThreePayloadCompile

structure SourceBinding where
  sourceBytesHash : String
  dependencyBytesHash : String
  modelHash : String
  checkerHash : String
  toolchainIdentity : String
  deriving DecidableEq, Repr

def sourceBindingFresh (expected actual : SourceBinding) : Bool :=
  decide (expected = actual)

theorem changed_source_binding_stale (expected actual : SourceBinding)
    (h : expected.sourceBytesHash ≠ actual.sourceBytesHash) :
    sourceBindingFresh expected actual = false := by
  have hne : expected ≠ actual := by
    intro heq
    exact h (congrArg SourceBinding.sourceBytesHash heq)
  simp [sourceBindingFresh, hne]

end ThreePayloadCompile
