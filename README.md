
# Generalized Algebra

A Lean 4 project for calculations with Generalized Algebraic Theory (GAT) signatures

Created by Jacob Neumann for his PhD thesis, **A Generalized Algebraic Theory of Directed Equality** (2025).

## oneGAT and nouGAT

The GAT signature language, which we refer to as `oneGAT` is the QIIT signature language from ['Constructing Quotient Inductive-Inductive Types by Altenkirch, Kaposi, and Kovács](https://dl.acm.org/doi/abs/10.1145/3290315), but (currently) without the *Pi-types with metatheoretic domain*. The definition of `oneGAT` is given in [signature.lean](GeneralizedAlgebra/signature.lean) and the `oneGAT`-to-String function is implemented in [ConPrinting.lean](GeneralizedAlgebra/ConPrinting.lean).

The purpose of this project is to provide a convenient syntax for defining `oneGAT` signatures, and for automatically generating the corresponding notions of algebra, homomorphism, displayed algebra, section, etc., as defined in the 'Constructing QIITs' paper and its [appendix](https://bitbucket.org/akaposi/finitaryqiit/raw/master/appendix.pdf). We call this syntax `nouGAT`. The `nouGAT`-to-`oneGAT` parser is implemented in [nouGAT.lean](GeneralizedAlgebra/nouGAT.lean), and the algebra-generation, displayed-algebra-generation, etc. in [AlgPrinting.lean](GeneralizedAlgebra/AlgPrinting.lean).

The `nouGAT` syntax uses named variables (instead of `oneGAT`'s de Bruijn indices), Russell-style universe U with implicit El (instead of Tarski-style, with explicit El), infix arrows for (dependent) functions (instead of explicit Pi's), and other syntactic sugar implemented or in-the-works. So, for instance, the GAT ℭ𝔞𝔱 of *categories* would be written in `nouGAT` as:
```
Obj : U,
Hom : Obj ⇒ Obj ⇒ U,
id : (X : Obj) ⇒ Hom X X,
comp : {X Y Z : Obj} ⇒ Hom Y Z ⇒ Hom X Y ⇒ Hom X Z,
lunit : {X Y : Obj} ⇒ (f : Hom X Y) ⇒
    comp (id Y) f ≡ f,
runit : {X Y : Obj} ⇒ (f : Hom X Y) ⇒
    comp f (id X) ≡ f,
assoc : {W X Y Z : Obj} ⇒ (e : Hom W X) ⇒ (f : Hom X Y) ⇒ (g : Hom Y Z) ⇒
    comp g (comp f e) ≡ comp (comp g f) e
```
and then this is compiled to the `oneGAT` signature
```
⋄ 
▷ U 
▷ Π 0 (Π 1 U) 
▷ Π 1 (El (1 @ 0 @ 0)) 
▷ Π 2 (Π 3 (Π 4 (Π (4 @ 1 @ 0) (Π (5 @ 3 @ 2) (El (6 @ 4 @ 2)))))) 
▷ Π 3 (Π 4 (Π (4 @ 1 @ 0) (Eq (3 @ 2 @ 1 @ 1 @ (4 @ 1) @ 0) 0))) 
▷ Π 4 (Π 5 (Π (5 @ 1 @ 0) (Eq (4 @ 2 @ 2 @ 1 @ 0 @ (5 @ 2)) 0))) 
▷ Π 5 (Π 6 (Π 7 (Π 8 (
    Π (8 @ 3 @ 2) (Π (9 @ 3 @ 2) (Π (10 @ 3 @ 2) (
    Eq 
        (9 @ 6 @ 5 @ 3 @ 0 @ (9 @ 6 @ 5 @ 4 @ 1 @ 2)) 
        (9 @ 6 @ 4 @ 3 @ (9 @ 5 @ 4 @ 3 @ 0 @ 1) @ 2)
    )))))))
```
and then the following (pseudo)Agda definition of ℭ𝔞𝔱-algebras (i.e. categories) can be automatically generated:
```
record ℭ𝔞𝔱-Alg where
    (Obj : Set)
    (Hom : Obj → Obj → Set)
    (id : (X : Obj) → Hom X X)
    (comp : (X : Obj) → (Y : Obj) → (Z : Obj) → Hom Y Z → Hom X Y → Hom X Z)
    (lunit : (X : Obj) → (Y : Obj) → (f : Hom X Y) → comp X Y Y (id Y) f = f)
    (runit : (X : Obj) → (Y : Obj) → (f : Hom X Y) → comp X X Y f (id X) = f)
    (assoc : (W : Obj) → (X : Obj) → (Y : Obj) → (Z : Obj) → (e : Hom W X) → (f : Hom X Y) → (g : Hom Y Z) → comp W X Z g (comp W X Y f e) = comp W Y Z (comp X Y Z g f) e)
```
and likewise for homomorphisms, displayed algebras, and so on.

In the future, we hope to implement the algebras, homomorphisms, displayed algebras, etc. as mathematical structures within Lean, but for now the functions in [AlgPrinting.lean](GeneralizedAlgebra/AlgPrinting.lean) simply output a string specifying (in pseudoAgda) what these structures should be.

## Example GATs

Currently, signatures are given in a "pretty" and "plain" form. The "plain" form will actually syntax-check, and produce a `oneGAT` signature. The "pretty" versions make use of `nouGAT` syntax which may not have been implemented yet, and therefore likely won't compile. The "pretty" versions are the ones used in the text of the thesis. The ultimate goal is to implement the missing syntax, so that the "pretty" versions will produce the same `oneGAT` signature as their "plain" counterpart.

See [GeneralizedAlgebra.lean](GeneralizedAlgebra.lean) for a listing of all the example GATs and a demonstration of their `oneGAT` representation, algebras, displayed algebras, etc.

- **Sets** — 𝔖𝔢𝔱
    - *Pretty:* [set.lean](GeneralizedAlgebra/pretty_signatures/set.lean)
    - *Plain*: [set.lean](GeneralizedAlgebra/signatures/set.lean)
- **Pointed sets** — 𝔓
    - *Pretty:* [pointed.lean](GeneralizedAlgebra/pretty_signatures/pointed.lean)
    - *Plain*: [pointed.lean](GeneralizedAlgebra/signatures/pointed.lean)
- **Bipointed sets** — 𝔅
    - *Pretty:* [bipointed.lean](GeneralizedAlgebra/pretty_signatures/bipointed.lean)
    - *Plain*: [bipointed.lean](GeneralizedAlgebra/signatures/bipointed.lean)
- **Natural Numbers** — 𝔑
    - *Pretty*: [nat.lean](GeneralizedAlgebra/pretty_signatures/nat.lean)
    - *Plain*: [nat.lean](GeneralizedAlgebra/signatures/nat.lean)
- **Even/Odd Natural Numbers** — 𝔈𝔒
    - *Pretty*: [evenodd.lean](GeneralizedAlgebra/pretty_signatures/evenodd.lean)
    - *Plain*: [evenodd.lean](GeneralizedAlgebra/signatures/evenodd.lean)
- **Quivers** — 𝔔𝔲𝔦𝔳
    - *Pretty:* [quiver.lean](GeneralizedAlgebra/pretty_signatures/quiver.lean)
    - *Plain*: [quiver.lean](GeneralizedAlgebra/signatures/quiver.lean)
- **Reflexive Quivers** — 𝔯𝔔𝔲𝔦𝔳
    - *Pretty:* [refl_quiver.lean](GeneralizedAlgebra/pretty_signatures/refl_quiver.lean)
    - *Plain*: [refl_quiver.lean](GeneralizedAlgebra/signatures/refl_quiver.lean)
- **Monoids** — 𝔐𝔬𝔫
    - *Pretty:* [monoid.lean](GeneralizedAlgebra/pretty_signatures/monoid.lean)
    - *Plain*: [monoid.lean](GeneralizedAlgebra/signatures/monoid.lean)
- **Preorders** — 𝔓𝔯𝔢𝔒𝔯𝔡
    - *Pretty:* [preorder.lean](GeneralizedAlgebra/pretty_signatures/preorder.lean)
    - *Plain*: [preorder.lean](GeneralizedAlgebra/signatures/preorder.lean)
- **Setoids** — 𝔖𝔢𝔱𝔬𝔦𝔡
    - *Pretty:* [setoid.lean](GeneralizedAlgebra/pretty_signatures/setoid.lean)
    - *Plain*: [setoid.lean](GeneralizedAlgebra/signatures/setoid.lean)
- **Categories** — ℭ𝔞𝔱
    - *Pretty:* [category.lean](GeneralizedAlgebra/pretty_signatures/category.lean)
    - *Plain*: [category.lean](GeneralizedAlgebra/signatures/category.lean)
- **Groupoids** — 𝔊𝔯𝔭𝔡
    - *Pretty:* [groupoid.lean](GeneralizedAlgebra/pretty_signatures/groupoid.lean)
    - *Plain*: [groupoid.lean](GeneralizedAlgebra/signatures/groupoid.lean)
- **Categories with Families (CwFs)** — ℭ𝔴𝔉
    - *Pretty:* [CwF.lean](GeneralizedAlgebra/pretty_signatures/CwF.lean)
    - *Plain*: [CwF.lean](GeneralizedAlgebra/signatures/CwF.lean)
- **Polarized Categories with Families (PCwFs)** — 𝔓ℭ𝔴𝔉
    - *Pretty:* [PCwF.lean](GeneralizedAlgebra/pretty_signatures/PCwF.lean)
    - *Plain*: [PCwF.lean](GeneralizedAlgebra/signatures/PCwF.lean)
- **Neutral-Polarized Categories with Families (NPCwFs)** — 𝔑𝔓ℭ𝔴𝔉
    - *Pretty:* [NPCwF.lean](GeneralizedAlgebra/pretty_signatures/NPCwF.lean)
    - *Plain*: [NPCwF.lean](GeneralizedAlgebra/signatures/NPCwF.lean)
