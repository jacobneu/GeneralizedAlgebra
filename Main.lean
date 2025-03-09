import «GeneralizedAlgebra»


def writeOneGAT (X : printData): IO Unit := do
  let currentDir ← IO.currentDir
  let outputFile := System.FilePath.join currentDir (System.FilePath.mk $ "output/" ++ X.gatNamePlain ++ ".oneGAT")
  IO.FS.writeFile outputFile $ Con_toString (X.gat.con)

def writeRecordAlg (X : printData): IO Unit := do
  let currentDir ← IO.currentDir
  let outputFile := System.FilePath.join currentDir (System.FilePath.mk $ "output/" ++ X.gatNamePlain ++ "-alg.record.pseudo.agda")
  match Alg X.gat (some X.gatName) with
    | some s => IO.FS.writeFile outputFile s
    | none => return ()

def doAll (f : printData → IO Unit) : IO Unit :=
  List.foldl (λ wr1 p2 => (do wr1; f p2)) (return ()) allGATs

def main : IO Unit := do
  doAll writeOneGAT
  doAll writeRecordAlg
  -- let currentDir ← IO.currentDir
  -- let indexFile := System.FilePath.join currentDir (System.FilePath.mk "output/list.txt")
  -- let outputFile := System.FilePath.join currentDir (System.FilePath.mk "output/output.txt")
  -- let index ← IO.FS.readFile indexFile
  -- let natList := List.map (Char.toNat) index.toList
  -- IO.println $ List.foldl (λ s s' => s!"{s}{NEWLINE}{s'}") "" natList
--   let foo := "
-- "
  -- let output := match DAlg 𝔅 (some "𝔅") ["P","p₀","p₁"] with | some s => s | none => ""
  -- IO.FS.writeFile outputFile $ output
