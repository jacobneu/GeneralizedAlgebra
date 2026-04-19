import GeneralizedAlgebra.eliminate.formats.StringFormat





-- def dalgFor sl := (parenFor sl) ++ "ᴰ"
-- def homFor sl := (parenFor sl) ++ "ᴹ"
-- def sectFor sl := (parenFor sl) ++ "ˢ"
open sfDecor

def psDecorate (s : String) : sfDecor → String
| sfId => s
| sfAlg => s ++ "ᴬ"
| sfOne => s ++ "₁"
| sfDalg => s ++ "ᴰ"
| sfHom => s ++ "ᴹ"
| sfSect => s ++ "ˢ"
| sfZero => s ++ "₀"

def psFormatLine (s : String) : sfDecor → String
| sfId => "  ▷ " ++ s
| _ => "   " ++ s

def psFormatWrapping (G : String) (topnames : List String) : sfDecor → List String × List String
| sfId => ([G ++ " = ◇"],[""])
| sfAlg => (["record " ++ G ++ "-Alg where "],[""])
| sfDalg => (["record " ++ G ++ "-DAlg (" ++ (String.intercalate "," topnames) ++ ") where"],[""])
| sfHom => (["record " ++ G ++ "-Hom (" ++ (String.intercalate "," (List.map (· ++ "₀") topnames)) ++ ") (" ++ (String.intercalate "," (List.map (· ++ "₁") topnames)) ++ ") where"],[""])
| sfSect => (["record " ++ G ++ "-Sect (" ++ (String.intercalate "," topnames) ++ ") (" ++ (String.intercalate "," (List.map (· ++ "ᴰ") topnames)) ++ ") where"],[""])
| sfOne => ([String.intercalate "," (List.map (· ++ "₁") topnames)],[])
| sfZero => ([String.intercalate "," (List.map (· ++ "₀") topnames)],[])

def pseudoAgda : StringFormat := ⟨
    λ sl => paren' " " sl [" "],
    String.intercalate " ",
    psDecorate,
    "Set",
    "=",
    "→",
    "⊤",
    ":",
    "{",
    "}",
    "U",
    (String.intercalate " " ["Π",·,·]),
    "Eq",
    "El",
    "@",
    "transp",
    "[wk]",
    psFormatWrapping,
    psFormatLine
⟩
