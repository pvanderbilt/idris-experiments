

Mod : Nat -> Type
Mod n = (k : Nat ** LT k n)


lemma_LTE_eq : LTE n n
lemma_LTE_eq {n = Z} = LTEZero
lemma_LTE_eq {n = (S k)} = LTESucc (lemma_LTE_eq {n=k})

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


modSucc : Mod n -> Mod n
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


