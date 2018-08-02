----------------------------------------------
-- Experiment: Fact
----------------------------------------------

data Fact : Type -> Type where
  Assert : {P : Type} -> (prf : P) -> Fact P

f1 : Fact (1+1 = 2)
f1 = Assert Refl

f2 : Fact ((length [1,2,3]) = 3)
f2 = Assert Refl

L3 : List Nat
L3 = [4,21,32]

f2a : Fact ((length L3) = 3)
f2a = Assert Refl


f3 : Fact ((i : Nat) -> 0 + i = i)
f3 = Assert (\_ => Refl)

f3' : Fact ((i : Nat) -> i + 0 = i)
f3' = Assert ZPR
  where 
    ZPR : (i : Nat) -> plus i Z = i
    ZPR Z = Refl
    ZPR (S k) = let recv = ZPR k in cong recv

ff : Fact (Fact (True=True))
ff = Assert (Assert Refl)
