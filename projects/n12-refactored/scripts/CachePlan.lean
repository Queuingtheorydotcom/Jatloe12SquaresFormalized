import Cache.Hashing

open Cache IO Hashing System in
def main (args : List String) : IO Unit := CacheM.run do
  let roots ← parseArgs ("lookup" :: args)
  if roots.isEmpty then throw <| IO.userError "Explicit cache roots required"
  let memo ← getHashMemo roots
  let hashes ← memo.filterByRootModules roots.keys
  let config : Array Lean.Json := hashes.fold (init := #[]) fun acc mod hash =>
    acc.push <| .mkObj [("module", .str mod.toString), ("file", .str hash.asLTar)]
  IO.println (Lean.Json.compress (.arr config))
