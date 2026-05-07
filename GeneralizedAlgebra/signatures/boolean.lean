import GeneralizedAlgebra.nouGAT_eliminate

def 𝔅𝔬𝔬𝔩 : GAT :=
⦃
  A : U,
  meet : A ⇒ A ⇒ A,
  join : A ⇒ A ⇒ A,
  not : A ⇒ A,
  top : A,
  bot : A,
  meetAssoc : {a b c : A} ⇒ meet a (meet b c) ≡ meet (meet a b) c,
  meetComm : {a b : A} ⇒ meet a b ≡ meet b a,
  meetIdent : {a : A} ⇒ meet a top ≡ a,
  meetCompl : {a : A} ⇒ meet a (not a) ≡ bot,
  joinAssoc : {a b c : A} ⇒ join a (join b c) ≡ join (join a b) c,
  joinComm : {a b : A} ⇒ join a b ≡ join b a,
  joinIdent : {a : A} ⇒ join a bot ≡ a,
  joinCompl : {a : A} ⇒ join a (not a) ≡ top,
  distr₁ : {a b c : A} ⇒ meet a (join b c) ≡ join (meet a b) (meet a c),
  distr₂ : {a b c : A} ⇒ join a (meet b c) ≡ meet (join a b) (join a c),
  absorb₁ : {a b : A} ⇒ meet a (join a b) ≡ a,
  absorb₂ : {a b : A} ⇒ join a (meet a b) ≡ a
⦄
