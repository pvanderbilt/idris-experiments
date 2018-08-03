module Modulus

%default total


-----------------------------------------------------------
--  The `Mod n` type
--    Represented by a Nat i and auxiliary Nat j = n-i-1
-----------------------------------------------------------

data Mod : Nat -> Type where
  MkMod : (i : Nat) -> (j : Nat) -> Mod (S (i + j))


-----------------------------------------------------------
--  Zero
-----------------------------------------------------------

ModZ : {j : Nat} -> Mod (S j)
ModZ {j} = MkMod Z j


-----------------------------------------------------------
--  Successor and predecessor
-----------------------------------------------------------

ModSucc : Mod n -> Mod n
ModSucc (MkMod i Z) =       let result = MkMod Z i 
                                goalSw = plusCommutative i Z
                            in rewrite goalSw in result
ModSucc (MkMod i' (S j')) = let result = MkMod (S i') j' 
                                goalSw = sym $ plusSuccRightSucc i' j'
                            in rewrite goalSw in result

ModPred : Mod n -> Mod n
ModPred (MkMod Z j) =       let result = MkMod j Z 
                                goalSw = plusCommutative Z j
                            in rewrite goalSw in result
ModPred (MkMod (S i') j') = let result = MkMod i' (S j') 
                                goalSw = plusSuccRightSucc i' j'
                            in rewrite goalSw in result

-----------------------------------------------------------
--  Addition
-----------------------------------------------------------

ModAdd : Mod n -> Mod n -> Mod n
ModAdd (MkMod Z _) y = y
ModAdd x@(MkMod (S i') j') y = ModSucc (ModAdd (assert_smaller (MkMod (S i') j') (ModPred x)) y)

-----------------------------------------------------------
--  Inverse
-----------------------------------------------------------

ModInv : Mod n -> Mod n
ModInv (MkMod Z j) = (MkMod Z j)
ModInv (MkMod (S i') j') = let result = MkMod (S j') i'
                               goalSw = plusCommutative i' j'
                           in rewrite goalSw in result


-----------------------------------------------------------
--  Axioms
--     axLZ : 0 + m = m
--     (the rest are TBD)
-----------------------------------------------------------

axLZ : (m : Mod (S _)) -> (ModAdd ModZ m) = m
axLZ i = Refl

axInv2isId : (m : Mod (S _)) -> (ModInv (ModInv m)) = m
axInv2isId (MkMod Z j) = Refl
axInv2isId (MkMod (S i') j') = let
                                 p1 : (ModInv (MkMod (S i') j') = MkMod (S j') i') = ?h1
                               in ?axInv2isId_rhs_4

{-   Replacing ?h1 by Refl gives a type mismatch:
 
   Specifically:
             Type mismatch between
                     MkMod (S j') i'
             and
                     rewrite__impl (\replaced => Mod (S (S replaced)))
                                   (plusCommutative i' j')
                                   (MkMod (S j') i')

-}


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
Nat2Mod Z p = MkMod Z p
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
