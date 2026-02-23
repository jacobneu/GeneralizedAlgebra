import GeneralizedAlgebra.signatures.pointed

def 𝔐𝔬𝔫_data : GATdata := [GATdata|
    M     : U,
    u     : M,
    m     : M ⇒ M ⇒ M,
    lunit : (x : M) ⇒ m u x ≡ x,
    runit : (x : M) ⇒ m x u ≡ x,
    assoc : (x : M) ⇒ (y : M) ⇒ (z : M) ⇒ m x (m y z) ≡ m (m x y) z
]

def 𝔐𝔬𝔫 : GAT := ⟨
    𝔐𝔬𝔫_data,
    by
        apply wellCon.wellCons

        -- (x : M) ⇒ (y : M) ⇒ (z : M) ⇒
        repeat
            apply wellTy.wellPI
            repeat apply @wellTm.wellWkTm _ preTy.preUU
            apply wellTm.wellZero
            apply wellTy.wellUU

        apply @wellTy.wellEQ _ (preTm.preVAR 7)
        -- M isType
        apply @wellTm.wellWkTm _ preTy.preUU _ (preTm.preVAR 6)
        apply @wellTm.wellWkTm _ preTy.preUU _ (preTm.preVAR 5)
        apply @wellTm.wellWkTm _ preTy.preUU _ (preTm.preVAR 4)
        apply @wellTm.wellWkTm _ preTy.preUU _ (preTm.preVAR 3)
        apply @wellTm.wellWkTm _ preTy.preUU _ (preTm.preVAR 2)
        apply @wellTm.wellWkTm _ preTy.preUU _ (preTm.preVAR 1)
        apply @wellTm.wellWkTm _ preTy.preUU _ (preTm.preVAR 0)
        apply wellTm.wellZero
        apply wellTy.wellUU
        -- m x (m y z) : M
        apply @wellTm.wellAPP _ (preTm.preVAR 7) (preTy.preEL $ preTm.preVAR 8)
        -- m x : M ⇒ M
        apply @wellTm.wellAPP _ (preTm.preVAR 7) (preTy.prePI (preTm.preVAR 8) (preTy.preEL (preTm.preVAR 9)))
        -- m : M ⇒ M ⇒ M
        apply @wellTm.wellWkTm _ (preTy.prePI (preTm.preVAR 6) (preTy.prePI (preTm.preVAR 7) (preTy.preEL (preTm.preVAR 8))))
        apply @wellTm.wellWkTm _ (preTy.prePI (preTm.preVAR 5) (preTy.prePI (preTm.preVAR 6) (preTy.preEL (preTm.preVAR 7))))
        apply @wellTm.wellWkTm _ (preTy.prePI (preTm.preVAR 4) (preTy.prePI (preTm.preVAR 5) (preTy.preEL (preTm.preVAR 6))))
        apply @wellTm.wellWkTm _ (preTy.prePI (preTm.preVAR 3) (preTy.prePI (preTm.preVAR 4) (preTy.preEL (preTm.preVAR 5))))
        apply @wellTm.wellWkTm _ (preTy.prePI (preTm.preVAR 2) (preTy.prePI (preTm.preVAR 3) (preTy.preEL (preTm.preVAR 4))))
        apply wellTm.wellZero


        repeat
            apply wellTy.wellPI
            repeat apply @wellTm.wellWkTm _ preTy.preUU
            apply wellTm.wellZero
            apply wellTy.wellUU
        repeat
            apply wellTy.wellEL
            repeat apply @wellTm.wellWkTm _ preTy.preUU
            apply wellTm.wellZero
            apply wellTy.wellUU
            apply wellTm.wellZero
        apply wellTy.wellEL
        repeat apply @wellTm.wellWkTm _ preTy.preUU
        apply wellTm.wellZero
        apply wellTy.wellUU

        -- x : M
        apply @wellTm.wellWkTm _ (preTy.preEL $ preTm.preVAR 6)
        apply @wellTm.wellWkTm _ (preTy.preEL $ preTm.preVAR 5)
        apply wellTm.wellZero
        apply wellTy.wellEL
        repeat apply @wellTm.wellWkTm _ preTy.preUU
        apply wellTm.wellZero
        apply wellTy.wellUU

        -- m y z : M
        apply @wellTm.wellAPP _ (preTm.preVAR 7) (preTy.preEL $ preTm.preVAR 8)
        -- m x : M ⇒ M
        apply @wellTm.wellAPP _ (preTm.preVAR 7) (preTy.prePI (preTm.preVAR 8) (preTy.preEL (preTm.preVAR 9)))
        -- m : M ⇒ M ⇒ M
        apply @wellTm.wellWkTm _ (preTy.prePI (preTm.preVAR 6) (preTy.prePI (preTm.preVAR 7) (preTy.preEL (preTm.preVAR 8))))
        apply @wellTm.wellWkTm _ (preTy.prePI (preTm.preVAR 5) (preTy.prePI (preTm.preVAR 6) (preTy.preEL (preTm.preVAR 7))))
        apply @wellTm.wellWkTm _ (preTy.prePI (preTm.preVAR 4) (preTy.prePI (preTm.preVAR 5) (preTy.preEL (preTm.preVAR 6))))
        apply @wellTm.wellWkTm _ (preTy.prePI (preTm.preVAR 3) (preTy.prePI (preTm.preVAR 4) (preTy.preEL (preTm.preVAR 5))))
        apply @wellTm.wellWkTm _ (preTy.prePI (preTm.preVAR 2) (preTy.prePI (preTm.preVAR 3) (preTy.preEL (preTm.preVAR 4))))
        apply wellTm.wellZero
        repeat
            apply wellTy.wellPI
            repeat apply @wellTm.wellWkTm _ preTy.preUU
            apply wellTm.wellZero
            apply wellTy.wellUU
        repeat
            apply wellTy.wellEL
            repeat apply @wellTm.wellWkTm _ preTy.preUU
            apply wellTm.wellZero
            apply wellTy.wellUU
            apply wellTm.wellZero

        apply wellTy.wellEL
        repeat apply @wellTm.wellWkTm _ preTy.preUU
        apply wellTm.wellZero
        apply wellTy.wellUU

        -- y : M
        apply @wellTm.wellWkTm _ (preTy.preEL $ preTm.preVAR 6)
        apply wellTm.wellZero
        apply wellTy.wellEL
        repeat apply @wellTm.wellWkTm _ preTy.preUU
        apply wellTm.wellZero
        apply wellTy.wellUU
        -- z : M
        apply wellTm.wellZero
        apply wellTy.wellEL
        repeat apply @wellTm.wellWkTm _ preTy.preUU
        apply wellTm.wellZero
        apply wellTy.wellUU

        -- m (m x y) z : M
        apply @wellTm.wellAPP _ (preTm.preVAR 7) (preTy.preEL $ preTm.preVAR 8)
        -- m x : M ⇒ M
        apply @wellTm.wellAPP _ (preTm.preVAR 7) (preTy.prePI (preTm.preVAR 8) (preTy.preEL (preTm.preVAR 9)))
        -- m : M ⇒ M ⇒ M
        apply @wellTm.wellWkTm _ (preTy.prePI (preTm.preVAR 6) (preTy.prePI (preTm.preVAR 7) (preTy.preEL (preTm.preVAR 8))))
        apply @wellTm.wellWkTm _ (preTy.prePI (preTm.preVAR 5) (preTy.prePI (preTm.preVAR 6) (preTy.preEL (preTm.preVAR 7))))
        apply @wellTm.wellWkTm _ (preTy.prePI (preTm.preVAR 4) (preTy.prePI (preTm.preVAR 5) (preTy.preEL (preTm.preVAR 6))))
        apply @wellTm.wellWkTm _ (preTy.prePI (preTm.preVAR 3) (preTy.prePI (preTm.preVAR 4) (preTy.preEL (preTm.preVAR 5))))
        apply @wellTm.wellWkTm _ (preTy.prePI (preTm.preVAR 2) (preTy.prePI (preTm.preVAR 3) (preTy.preEL (preTm.preVAR 4))))
        apply wellTm.wellZero


        repeat
            apply wellTy.wellPI
            repeat apply @wellTm.wellWkTm _ preTy.preUU
            apply wellTm.wellZero
            apply wellTy.wellUU
        repeat
            apply wellTy.wellEL
            repeat apply @wellTm.wellWkTm _ preTy.preUU
            apply wellTm.wellZero
            apply wellTy.wellUU
            apply wellTm.wellZero
        apply wellTy.wellEL
        repeat apply @wellTm.wellWkTm _ preTy.preUU
        apply wellTm.wellZero
        apply wellTy.wellUU

        -- m x y : M
        apply @wellTm.wellAPP _ (preTm.preVAR 7) (preTy.preEL $ preTm.preVAR 8)
        -- m x : M ⇒ M
        apply @wellTm.wellAPP _ (preTm.preVAR 7) (preTy.prePI (preTm.preVAR 8) (preTy.preEL (preTm.preVAR 9)))
        -- m : M ⇒ M ⇒ M
        apply @wellTm.wellWkTm _ (preTy.prePI (preTm.preVAR 6) (preTy.prePI (preTm.preVAR 7) (preTy.preEL (preTm.preVAR 8))))
        apply @wellTm.wellWkTm _ (preTy.prePI (preTm.preVAR 5) (preTy.prePI (preTm.preVAR 6) (preTy.preEL (preTm.preVAR 7))))
        apply @wellTm.wellWkTm _ (preTy.prePI (preTm.preVAR 4) (preTy.prePI (preTm.preVAR 5) (preTy.preEL (preTm.preVAR 6))))
        apply @wellTm.wellWkTm _ (preTy.prePI (preTm.preVAR 3) (preTy.prePI (preTm.preVAR 4) (preTy.preEL (preTm.preVAR 5))))
        apply @wellTm.wellWkTm _ (preTy.prePI (preTm.preVAR 2) (preTy.prePI (preTm.preVAR 3) (preTy.preEL (preTm.preVAR 4))))
        apply wellTm.wellZero
        repeat
            apply wellTy.wellPI
            repeat apply @wellTm.wellWkTm _ preTy.preUU
            apply wellTm.wellZero
            apply wellTy.wellUU
        repeat
            apply wellTy.wellEL
            repeat apply @wellTm.wellWkTm _ preTy.preUU
            apply wellTm.wellZero
            apply wellTy.wellUU
            apply wellTm.wellZero
        apply wellTy.wellEL
        repeat apply @wellTm.wellWkTm _ preTy.preUU
        apply wellTm.wellZero
        apply wellTy.wellUU


        repeat
            apply wellTy.wellPI
            repeat apply @wellTm.wellWkTm _ preTy.preUU
            apply wellTm.wellZero
            apply wellTy.wellUU
        repeat
            apply wellTy.wellEL
            repeat apply @wellTm.wellWkTm _ preTy.preUU
            apply wellTm.wellZero
            apply wellTy.wellUU
            apply wellTm.wellZero

        -- x : M
        apply @wellTm.wellWkTm _ (preTy.preEL $ preTm.preVAR 6)
        apply @wellTm.wellWkTm _ (preTy.preEL $ preTm.preVAR 5)
        apply wellTm.wellZero
        apply wellTy.wellEL
        repeat apply @wellTm.wellWkTm _ preTy.preUU
        apply wellTm.wellZero
        apply wellTy.wellUU

        -- y : M
        apply @wellTm.wellWkTm _ (preTy.preEL $ preTm.preVAR 6)
        apply wellTm.wellZero
        apply wellTy.wellEL
        repeat apply @wellTm.wellWkTm _ preTy.preUU
        apply wellTm.wellZero
        apply wellTy.wellUU

        -- z : M
        apply wellTm.wellZero
        apply wellTy.wellEL
        repeat apply @wellTm.wellWkTm _ preTy.preUU
        apply wellTm.wellZero
        apply wellTy.wellUU

        apply wellCon.wellCons

        apply wellTy.wellPI
        repeat apply @wellTm.wellWkTm _ preTy.preUU
        apply wellTm.wellZero
        apply wellTy.wellUU
        -- m u x ≡ x
        apply @wellTy.wellEQ _ (preTm.preVAR 4)
        -- M isType
        apply @wellTm.wellWkTm _ preTy.preUU _ (preTm.preVAR 3)
        apply @wellTm.wellWkTm _ preTy.preUU _ (preTm.preVAR 2)
        apply @wellTm.wellWkTm _ preTy.preUU _ (preTm.preVAR 1)
        apply @wellTm.wellWkTm _ preTy.preUU _ (preTm.preVAR 0)
        apply wellTm.wellZero
        apply wellTy.wellUU
        -- m x u : M
        apply @wellTm.wellAPP _ (preTm.preVAR 4) (preTy.preEL $ preTm.preVAR 5)
        -- m x : M ⇒ M
        apply @wellTm.wellAPP _ (preTm.preVAR 4) (preTy.prePI (preTm.preVAR 5) (preTy.preEL (preTm.preVAR 6)))
        -- m : M ⇒ M ⇒ M
        apply @wellTm.wellWkTm _ (preTy.prePI (preTm.preVAR 3) (preTy.prePI (preTm.preVAR 4) (preTy.preEL (preTm.preVAR 5))))
        apply @wellTm.wellWkTm _ (preTy.prePI (preTm.preVAR 2) (preTy.prePI (preTm.preVAR 3) (preTy.preEL (preTm.preVAR 4))))
        apply wellTm.wellZero

        repeat
            apply wellTy.wellPI
            repeat apply @wellTm.wellWkTm _ preTy.preUU
            apply wellTm.wellZero
            apply wellTy.wellUU
        repeat
            apply wellTy.wellEL
            repeat apply @wellTm.wellWkTm _ preTy.preUU
            apply wellTm.wellZero
            apply wellTy.wellUU
            apply wellTm.wellZero

        apply wellTy.wellEL
        repeat apply @wellTm.wellWkTm _ preTy.preUU
        apply wellTm.wellZero
        apply wellTy.wellUU

        -- u : M
        apply @wellTm.wellWkTm _ (preTy.preEL $ preTm.preVAR 3)
        apply @wellTm.wellWkTm _ (preTy.preEL $ preTm.preVAR 2)
        apply @wellTm.wellWkTm _ (preTy.preEL $ preTm.preVAR 1)
        apply wellTm.wellZero
        apply wellTy.wellEL
        apply wellTm.wellZero
        apply wellTy.wellUU

        apply wellTm.wellZero
        apply wellTy.wellEL
        repeat apply @wellTm.wellWkTm _ preTy.preUU
        apply wellTm.wellZero
        apply wellTy.wellUU



        apply wellCon.wellCons
        apply wellTy.wellPI
        repeat apply @wellTm.wellWkTm _ preTy.preUU
        apply wellTm.wellZero
        apply wellTy.wellUU
        -- m u x ≡ x
        apply @wellTy.wellEQ _ (preTm.preVAR 3)
        -- M isType
        apply @wellTm.wellWkTm _ preTy.preUU _ (preTm.preVAR 2)
        apply @wellTm.wellWkTm _ preTy.preUU _ (preTm.preVAR 1)
        apply @wellTm.wellWkTm _ preTy.preUU _ (preTm.preVAR 0)
        apply wellTm.wellZero
        apply wellTy.wellUU
        -- m u x : M
        apply @wellTm.wellAPP _ (preTm.preVAR 3) (preTy.preEL $ preTm.preVAR 4)
        -- m u : M ⇒ M
        apply @wellTm.wellAPP _ (preTm.preVAR 3) (preTy.prePI (preTm.preVAR 4) (preTy.preEL (preTm.preVAR 5)))
        -- m : M ⇒ M ⇒ M
        apply @wellTm.wellWkTm _ (preTy.prePI (preTm.preVAR 2) (preTy.prePI (preTm.preVAR 3) (preTy.preEL (preTm.preVAR 4))))
        apply wellTm.wellZero
        -- M ⇒ M ⇒ M isType
        repeat
            apply wellTy.wellPI
            repeat apply @wellTm.wellWkTm _ preTy.preUU
            apply wellTm.wellZero
            apply wellTy.wellUU
        apply wellTy.wellEL
        repeat apply @wellTm.wellWkTm _ preTy.preUU
        apply wellTm.wellZero
        apply wellTy.wellUU
        -- u : M
        apply @wellTm.wellWkTm _ (preTy.preEL $ preTm.preVAR 2)
        apply @wellTm.wellWkTm _ (preTy.preEL $ preTm.preVAR 1)
        apply wellTm.wellZero
        apply wellTy.wellEL
        apply wellTm.wellZero
        apply wellTy.wellUU

        -- x : M
        repeat
            apply wellTm.wellZero
            apply wellTy.wellEL
            repeat apply @wellTm.wellWkTm _ preTy.preUU
            apply wellTm.wellZero
            apply wellTy.wellUU



        -- M ⇒ M ⇒ M
        apply wellCon.wellCons
        apply wellTy.wellPI
        repeat apply @wellTm.wellWkTm _ preTy.preUU
        apply wellTm.wellZero
        apply wellTy.wellUU
        apply wellTy.wellPI
        repeat apply @wellTm.wellWkTm _ preTy.preUU
        apply wellTm.wellZero
        apply wellTy.wellUU
        apply wellTy.wellEL
        repeat apply @wellTm.wellWkTm _ preTy.preUU
        apply wellTm.wellZero
        apply wellTy.wellUU

        -- Pointed
        exact 𝔓.2

⟩
