data Mod : Nat -> Type where
  MkMod : (k : Nat) -> (plt : LT k n) -> Mod n

modv : Mod (S p) -> Nat
modv (MkMod k _) = k

modp : (m : Mod (S p)) -> LT (modv m) (S p)
modp (MkMod k plt) = plt

lemma_LtePrfEq : (p1, p2 : LTE i j) -> p1 = p2
lemma_LtePrfEq LTEZero LTEZero = Refl
lemma_LtePrfEq (LTESucc p1') (LTESucc p2') = let Refl = lemma_LtePrfEq p1' p2' in Refl

--lemma_modeq : (m1, m2 : Mod (S n')) -> (modv m1) = (modv m2) -> (modp m1) = (modp m2)
-- lemma_modeq (MkMod k p1) (MkMod k p2) Refl = lemma_LtePrfEq p1 p2

lemma_modeq : (m1, m2 : Mod (S n')) -> (modv m1) = (modv m2) -> m1 = m2
lemma_modeq (MkMod j p1) (MkMod j p2) Refl = let Refl = lemma_LtePrfEq p1 p2 in Refl




{- OLDER version (but below is even older)
Mod : Nat -> Type
Mod n = (k : Nat ** LT k n)

modv : Mod (S p) -> Nat
modv (k ** _) = k

modp : (m : Mod (S p)) -> LT (modv m) (S p)
modp (k ** pf) = pf

lemma_modeq : (m1, m2 : Mod (S p)) -> (modv m1) = (modv m2) -> (modp m1) = (modp m2)
lemma_modeq (k1 ** pf1) (k2 ** pf2) prf = ?lemma_modeq_rhs_2
-}


lemma_LTE_eq : LTE n n
lemma_LTE_eq {n = Z} = LTEZero
lemma_LTE_eq {n = (S k)} = LTESucc (lemma_LTE_eq {n=k})

lemma_LTE_S_R : LTE i j -> LTE i (S j)
lemma_LTE_S_R LTEZero = LTEZero
lemma_LTE_S_R (LTESucc x) = LTESucc $ lemma_LTE_S_R x 

{-
Lemma_LTE_Either : (n,m : Nat) -> LTE n m -> Either (n = m) (LT n m)
Lemma_LTE_Either Z Z LTEZero = Left Refl
Lemma_LTE_Either Z (S k) LTEZero = Right $ LTESucc LTEZero
Lemma_LTE_Either (S i) (S j) (LTESucc p) with (Lemma_LTE_Either i j p)
  Lemma_LTE_Either (S i) (S j) (LTESucc _) | (Left peq) = Left $ cong peq
  Lemma_LTE_Either (S i) (S j) (LTESucc _) | (Right plt) = Right $ LTESucc plt

Lemma_LTE_NE : (n,m : Nat) -> LTE n m -> ((n = m) -> Void) -> (LT n m)
Lemma_LTE_NE n m plte pneq with (Lemma_LTE_Either n m plte)
  Lemma_LTE_NE n m plte pneq | (Left peq) = absurd (pneq peq)
  Lemma_LTE_NE n m plte pneq | (Right plt) = plt

-}

modPred : Mod n -> Mod n
modPred {n = Z} (MkMod _ plt) impossible
modPred {n = (S p)} (MkMod Z plt) = (MkMod p lemma_LTE_eq)
modPred {n = (S p)} (MkMod (S k) (LTESucc plt)) = MkMod k $ lemma_LTE_S_R plt

modSucc : Mod n -> Mod n
modSucc {n = Z} (MkMod _ plt) impossible
modSucc {n = (S p)} (MkMod k (LTESucc x)) = ?modSucc_rhs_2


{-
modSucc {n = n} (k ** plt) with (decEq (S k) n)
  modSucc {n = (S k)} _      | (Yes Refl)  = (Z ** (LTESucc LTEZero))
  modSucc {n = n} (k ** plt) | (No contra) = let pslt = Lemma_LTE_NE (S k) n plt contra 
                                             in  ((S k) ** pslt)
modPred : Mod n -> Mod n
modPred {n = Z} (_ ** plt) = absurd plt
modPred {n = (S k)} (Z ** plt) = (k ** lemma_LTE_eq)
modPred {n = (S k)} ((S p) ** (LTESucc plt')) = (p ** ?h)


data IsTrue : Bool -> Type where
  ItsTrue : IsTrue True


Mod5 : Type
Mod5 = (n : Nat ** IsTrue $ lt n 5)

incr : Mod5 -> Mod5
incr (k ** prf) with (S k == 5)
  incr (k ** prf) | False = (k ** prf)
  incr (k ** prf) | True = (Z ** ItsTrue)

addMod : Mod5 -> Mod5 -> Mod5
addMod (Z ** pf) y = y
addMod ((S p) ** pf) y = incr (addMod (p ** ?pf_1) y)


-}
