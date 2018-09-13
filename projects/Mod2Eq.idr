module Modulus

%default total


-----------------------------------------------------------
--  The `Mod n` type
--    Represented by a Nat i and auxiliaries 
--       Nat j 
--       Invariant p : n = i+j+1
-----------------------------------------------------------

data Mod : Nat -> Type where
  MkMod : (i : Nat) -> (j : Nat) -> (p : n = (S (i + j))) -> Mod n

-----------------------------------------------------------
--  Zero
-----------------------------------------------------------


ModZ : {j : Nat} -> Mod (S j)
ModZ {j} = MkMod Z j Refl

--ModZ : Mod (S _)
--ModZ = MkMod Z _ Refl


-----------------------------------------------------------
--  Successor and predecessor
-----------------------------------------------------------

ModSucc : Mod n -> Mod n
ModSucc (MkMod i Z p)       = let peq = trans p $ cong {f=S} $ plusCommutative i Z
                              in MkMod Z i peq
ModSucc (MkMod i' (S j') p) = let peq = trans p $ cong {f=S} $ sym $ plusSuccRightSucc i' j'
                              in MkMod (S i') j' peq

ModPred : Mod n -> Mod n
ModPred (MkMod Z j p)       = MkMod j Z (trans p $ cong {f=S} $ plusCommutative Z j)
ModPred (MkMod (S i') j' p) = MkMod i' (S j') $ trans p $ cong {f=S}  $ plusSuccRightSucc i' j'

-----------------------------------------------------------
--  Addition
-----------------------------------------------------------

ModAdd : Mod n -> Mod n -> Mod n
ModAdd (MkMod Z _ _) y = y
ModAdd x@(MkMod (S i') j' p) y = ModSucc (ModAdd (assert_smaller x (ModPred x)) y)

-----------------------------------------------------------
--  Inverse
-----------------------------------------------------------

ModInv : Mod n -> Mod n
ModInv (MkMod Z j p) = (MkMod Z j p)
ModInv (MkMod (S i') j' p) = let peq = trans p $ cong {f=S . S} $ plusCommutative i' j'
                             in MkMod (S j') i' peq

-----------------------------------------------------------
--  Axioms
--     axInv2isId: ModInv is its own inverse
--     axLZ : 0 + m = m
--     axRZ : m + 0 = m
--     (the rest are TBD)
-----------------------------------------------------------

axLZ : (m : Mod (S _)) -> (ModAdd ModZ m) = m
axLZ m = Refl

axRZ : (m : Mod (S p)) -> (ModAdd m ModZ) = m
axRZ (MkMod Z j peq) = ?axRZ_rhs_2
axRZ {p = Z} (MkMod (S _) Z Refl) impossible
axRZ {p = Z} (MkMod (S _) (S _) Refl) impossible
axRZ {p = (S i)} (MkMod (S k) j peq) = ?axRZ_rhs_4

{-
axRZ {p = Z} (MkMod Z Z Refl) = Refl
axRZ {p = Z} (MkMod Z (S _) Refl) impossible
axRZ {p = Z} (MkMod (S _) _ Refl) impossible
axRZ {p = (S k)} (MkMod Z j p) = ?axRZ_rhs_2
axRZ {p = (S k)} (MkMod (S i) j p) = ?axRZ_rhs_3

axRZ (MkMod i Z p) = ?axRZ_rhs_2
axRZ (MkMod i (S k) p) = ?axRZ_rhs_3
-}
lemTransAssoc : (p,q,r : _) -> (trans p (trans q r)) = (trans (trans p q) r)
lemTransAssoc Refl Refl Refl = Refl

lemTransReflId : (p : _) -> (trans p Refl) = p
lemTransReflId Refl = Refl

lemTransSymId : (p, q : _) -> q = sym p -> trans p q = Refl
lemTransSymId Refl (sym Refl) Refl = Refl

lemEq2 : {x,y : Nat} -> (p1, p2 : x = y) -> p1 = p2
lemEq2 Refl Refl = Refl

lemTransAp : (f : a->b) -> (trans p1 p2) = Refl -> (trans (cong {f=f} p1) (cong {f=f} p2) = Refl)
lemTransAp {p1 = Refl} {p2 = Refl} f prf = Refl

lemTransRefl : {x,y : a} -> (p1 : x = y) -> (p2 : y = x) -> (trans p1 p2) = Refl
lemTransRefl Refl Refl = Refl

axInv2isId : (m : Mod n) -> (ModInv (ModInv m)) = m
axInv2isId (MkMod Z _ _) = Refl
axInv2isId (MkMod (S i') j' p) =
  let
    goal4 : (trans (plusCommutative i' j') (plusCommutative j' i') = Refl) = lemTransRefl _ _
    -- goal4 : (trans (plusCommutative i' j') (plusCommutative j' i') = Refl) 
    --         = lemTransSymId (plusCommutative i' j') (plusCommutative j' i') ?h4
    goal3 : ((trans (cong {f=S . S} (plusCommutative i' j')) 
                    (cong {f=S . S} (plusCommutative j' i'))) = Refl) = lemTransAp (S . S) goal4
    goal3ap = cong {f = trans p} goal3
    goal2 : (trans p (trans (cong {f=S . S} (plusCommutative i' j'))
                            (cong {f=S . S} (plusCommutative j' i')) ) = p) = trans goal3ap (lemTransReflId p)
    ptrans = sym $ lemTransAssoc p (cong {f=S . S} (plusCommutative i' j')) (cong {f=S . S} (plusCommutative j' i'))
    goal1 : ((trans (trans p (cong {f=S . S} (plusCommutative i' j')))
                    (cong {f=S . S} (plusCommutative j' i'))) = p) = trans ptrans goal2
  in cong {f = MkMod (S i') j'} goal1

axInv2isId' : (m : Mod n) -> (ModInv (ModInv m)) = m
axInv2isId' (MkMod Z _ _) = Refl
axInv2isId' (MkMod (S i') j' p) = cong {f = MkMod (S i') j'} goal1
  where
    -- goal4 : (trans (plusCommutative i' j') (plusCommutative j' i') = Refl)
    -- goal4 = lemTransRefl (plusCommutative i' j') (plusCommutative j' i') 
    -- goal3 = lemTransAp (S . S) goal4
    goal3 : ((trans (cong {f=S . S} (plusCommutative i' j')) (cong {f=S . S} (plusCommutative j' i'))) = Refl)
    goal3 = lemTransRefl _ _ 
    goal2 : (trans p (trans (cong {f=S . S} (plusCommutative i' j'))
                            (cong {f=S . S} (plusCommutative j' i')) ) = p)
    goal2 = trans (cong {f = trans p} goal3) (lemTransReflId p)
    goal1 : ((trans (trans p (cong {f=S . S} (plusCommutative i' j')))
                    (cong {f=S . S} (plusCommutative j' i'))) = p)
    goal1 = let
              ptrans = sym $ lemTransAssoc p (cong {f=S . S} (plusCommutative i' j')) (cong {f=S . S} (plusCommutative j' i'))
            in trans ptrans goal2

 
lemALL : {x,y,n : a} -> (p0 : n = x) -> (p1 : x = y) -> (p2 : y = x) -> (trans (trans p0 p1) p2) = p0
lemALL Refl Refl Refl = Refl

axInv2isId'' : (m : Mod n) -> (ModInv (ModInv m)) = m
axInv2isId'' (MkMod Z _ _) = Refl
axInv2isId'' (MkMod (S i') j' p) = cong {f = MkMod (S i') j'} $ lemALL _ _ _

------+++++ STUFF

Modv : Mod n -> Nat
Modv (MkMod i j p) = i

ModEq : (m1, m2 : Mod n) -> Type
ModEq m1 m2 = (Modv m1 = Modv m2)
--ModEq (MkMod i1 j1 p1) (MkMod i2 j2 p2) = (i1 = i2)

lemAddRInj : (x,y1,y2 : Nat) -> (x+y1)=(x+y2) -> y1=y2
lemAddRInj Z y1 y2 prf = prf
lemAddRInj (S x') y1 y2 prf = lemAddRInj x' y1 y2 $ succInjective _ _ prf

lemEq3 :  {x,y1,y2 : Nat} -> (p1 : x = y1) -> (p2 : x = y2) -> (y1 = y2, p1 = p2)
lemEq3 Refl Refl = (Refl, Refl)

{- OK, works
lemEqIsId : (m1, m2 : Mod (S n')) -> ModEq m1 m2 -> m1 = m2
lemEqIsId (MkMod i j1 p1) (MkMod i j2 p2) Refl = 
  let 
    (peq, ppeq) = lemEq3 p1 p2 
    Refl = lemAddInj {y1=j1} {y2=j2} $ succInjective _ _ peq
-- xxx = cong {f = MkMod i} peq2
  in (case ppeq of
           Refl => Refl)
-}

lemEqPrfsEq : (p1, p2 : x = y) -> p1 = p2
lemEqPrfsEq Refl Refl = Refl

lemEqIsId : (m1, m2 : Mod (S n')) -> ModEq m1 m2 -> m1 = m2
lemEqIsId (MkMod i j1 p1) (MkMod i j2 p2) Refl = 
  let
    prhss : (i + j1 = i + j2) = succInjective _ _ $ trans (sym p1) p2
    Refl  : (j1 = j2) = lemAddRInj i j1 j2 prhss
    peq   : (p1 = p2) = lemEqPrfsEq p1 p2
  in cong peq

predSuccIsId : (m : Mod (S n')) -> ModPred (ModSucc m) = m
predSuccIsId (MkMod i Z p) = lemEqIsId _ _ Refl
predSuccIsId (MkMod i (S k) p) = lemEqIsId _ _ Refl

lemModPredS : (m : Mod (S _)) -> Modv m = (S k) -> Modv (ModPred m) = k
lemModPredS (MkMod Z _ _) Refl impossible
lemModPredS (MkMod (S k) j p) Refl = Refl

lemModPredZ : (m : Mod (S p)) -> Modv m = Z -> Modv (ModPred m) = p
lemModPredZ (MkMod Z j peq) Refl = succInjective _ _ $ sym peq -- ?lemModPredZ_rhs_1
lemModPredZ (MkMod (S _) _ _) Refl impossible

{- In progress, may need lemmas above 
axLR : (m : Mod (S n')) -> (ModAdd m ModZ) = m
axLR {n' = (Z + j)} (MkMod Z j Refl) = Refl
--axLR {n' = ((S k) + j)} (MkMod (S k) j Refl) = ?axLR_rhs_1
axLR (MkMod (S k) j Refl) = ?axLR_rhs_3

-- let m = (MkMod (S k) j Refl) in (ModAdd m (MkMod Z (S (k + j)) Refl)) = m

-- let p1 : ((Z1 + j) = j) = succInjective _ _ Refl in
-}
{-
axLR {n'} (MkMod Z n' Refl) = Refl
axLR {n'} (MkMod (S k) j p) = 
  let
    ihp : (S n' = S (k + (S j))) = ?hih
    ih = axLR $ MkMod k (S j) ihp
  in ?axLR_rhs_3
-}
-- let p1 : (m = j) = succInjective _ _ p in rewrite p1 in Refl
{-

{- In progress: TBD: finish ?h3
axLR : (m : Mod (S _)) -> (ModAdd m ModZ) = m
axLR (MkMod Z _) = Refl
axLR (MkMod (S i') j') = ?h_3
-}

{-
    In progress
axInvR : (m : Mod (S _)) -> (ModAdd m (ModInv m)) = ModZ
axInvR (MkMod Z j) = Refl
axInvR (MkMod (S i') j') = let recv = axInvR (assert_smaller (MkMod (S i') j') (MkMod i' (S j')))
                           in ?h -- rewrite (plusSuccRightSucc i' j') in ?h -- recv -- Refl
-- switched!!
--  ModAdd (ModInv (MkMod (S i') j')) (MkMod (S i') j')
--  = ModAdd (MkMod (S j') i') (MkMod (S i') j')
--  = ModSucc (ModAdd (MkMod j' (S i')) (MkMod (S i') j'))

-- recv = ModSucc (ModAdd (MkMod (S j') i') (MkMod i' (S j')))
-}



-----------------------------------------------------------
--  Nat2Mod: A useful function to convert Nats to Mod n.
-----------------------------------------------------------

Nat2Mod : Nat -> (p : Nat) -> Mod (S p)
Nat2Mod Z p = MkMod Z p Refl
Nat2Mod (S k) p = ModSucc (Nat2Mod k p) 



-----------------------------------------------------------
--  Other stuff that didn't or isn't working out
-----------------------------------------------------------


axLZ' : (i : Nat) -> {j : Nat} -> (ModAdd ModZ (MkMod i j)) = (MkMod i j)
axLZ' i = Refl


{-
--ModAdd' : Mod n -> Mod n -> Mod n
--ModAdd' (MkMod ix _) (MkMod iy _) = ?ModAdd'_rhs_1

ModAdd'' : (nx, ny : Nat) -> (nx = ny) -> Mod nx -> Mod ny -> Mod ny
ModAdd'' (S (ix + jx)) (S (iy + jy)) prf (MkMod ix jx) (MkMod iy jy) = ?ModAdd''_rhs_1
-}
-}
