
# Generalized Algebra

A Lean 4 project for calculations with Generalized Algebraic Theory (GAT) signatures

Created by Jacob Neumann for his PhD thesis, **A Generalized Algebraic Theory of Directed Equality** (2025).


## Example signatures

Currently, signatures are given in a "pretty" and "plain" form. The "plain" form will actually syntax-check, and produce a `oneGAT` signature. The "pretty" versions make use of `nouGAT` syntax which may not have been implemented yet, and therefore likely won't compile. The "pretty" versions are the ones used in the text of the thesis. The ultimate goal is to implement the missing syntax, so that the "pretty" versions will produce the same `oneGAT` signature as their "plain" counterpart.

- **Pointed sets** — $\mathfrak{P}$
    - *Pretty:* [pointed.lean](GeneralizedAlgebra/pretty_signatures/pointed.lean)
    - *Plain*: [pointed.lean](GeneralizedAlgebra/signatures/pointed.lean)
- **Natural Numbers**
    - *Pretty: [nat.lean](GeneralizedAlgebra/pretty_signatures/nat.lean)*
    - *Plain*: [nat.lean](GeneralizedAlgebra/signatures/nat.lean)
- **Quivers**
    - *Pretty:* [quiver.lean](GeneralizedAlgebra/pretty_signatures/quiver.lean)
    - *Plain*: [quiver.lean](GeneralizedAlgebra/signatures/quiver.lean)
- **Reflexive Quivers**
    - *Pretty:* [refl_quiver.lean](GeneralizedAlgebra/pretty_signatures/refl_quiver.lean)
    - *Plain*: [refl_quiver.lean](GeneralizedAlgebra/signatures/refl_quiver.lean)
- **Monoids**
    - *Pretty:* [monoid.lean](GeneralizedAlgebra/pretty_signatures/monoid.lean)
    - *Plain*: [monoid.lean](GeneralizedAlgebra/signatures/monoid.lean)
- **Preorders**
    - *Pretty:* [preorder.lean](GeneralizedAlgebra/pretty_signatures/preorder.lean)
    - *Plain*: [preorder.lean](GeneralizedAlgebra/signatures/preorder.lean)
- **Setoids**
    - *Pretty:* [setoid.lean](GeneralizedAlgebra/pretty_signatures/setoid.lean)
    - *Plain*: [setoid.lean](GeneralizedAlgebra/signatures/setoid.lean)
- **Categories**
    - *Pretty:* [category.lean](GeneralizedAlgebra/pretty_signatures/category.lean)
    - *Plain*: [category.lean](GeneralizedAlgebra/signatures/category.lean)
- **Groupoids**
    - *Pretty:* [groupoid.lean](GeneralizedAlgebra/pretty_signatures/groupoid.lean)
    - *Plain*: [groupoid.lean](GeneralizedAlgebra/signatures/groupoid.lean)
- **Categories with Families (CwFs)**
    - *Pretty:* [CwF.lean](GeneralizedAlgebra/pretty_signatures/CwF.lean)
    - *Plain*: [CwF.lean](GeneralizedAlgebra/signatures/CwF.lean)
- **Polarized Categories with Families (PCwFs)**
    - *Pretty:* [PCwF.lean](GeneralizedAlgebra/pretty_signatures/PCwF.lean)
    - *Plain*: [PCwF.lean](GeneralizedAlgebra/signatures/PCwF.lean)
- **Neutral-Polarized Categories with Families (NPCwFs)**
    - *Pretty:* [NPCwF.lean](GeneralizedAlgebra/pretty_signatures/NPCwF.lean)
    - *Plain*: [NPCwF.lean](GeneralizedAlgebra/signatures/NPCwF.lean)