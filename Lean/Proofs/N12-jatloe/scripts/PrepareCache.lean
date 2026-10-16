import Cache.IO

/-! Runtime setup for an explicitly requested remote replay, not a proof root.
Uses the unchanged pinned Mathlib installer and its platform-specific leantar. -/
def main : IO Unit := do
  Cache.IO.validateLeanTar
  IO.println "leantar setup complete"
