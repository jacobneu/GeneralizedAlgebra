import GeneralizedAlgebra.eliminate.formats.StringFormat





-- def dalgFor sl := (parenFor sl) ++ "ᴰ"
-- def homFor sl := (parenFor sl) ++ "ᴹ"
-- def sectFor sl := (parenFor sl) ++ "ˢ"

def pseudoAgda : StringFormat := ⟨
    λ sl => paren' " " sl [" "],
    String.intercalate " ",
    (· ++ "ᴰ"),
    (· ++ "ᴹ"),
    (· ++ "ˢ"),
    (· ++ "₀"),
    (· ++ "₁")
⟩
