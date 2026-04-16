import GeneralizedAlgebra.eliminate.formats.StringFormat





-- def dalgFor sl := (parenFor sl) ++ "ᴰ"
-- def homFor sl := (parenFor sl) ++ "ᴹ"
-- def sectFor sl := (parenFor sl) ++ "ˢ"
open sfDecor

def psDecorate (s : String) : sfDecor → String
| sfId => s
| sfOne => s ++ "₁"
| sfDalg => s ++ "ᴰ"
| sfHom => s ++ "ᴹ"
| sfSect => s ++ "ˢ"
| sfZero => s ++ "₀"

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
    "}"
⟩
