import Data.List
import Data.Vect

--------------------------------------------------------------------------------
-- An attempt at showing Permutations for a group
--     Motivated by Adrian's attempt
--     This uses vectors and a 'permutation code' which 
--       specifies a permutation independent of its starting value
--------------------------------------------------------------------------------

---+------------------------------------------
---+  Adrian's definition of a permutation
---+------------------------------------------

data Perm : List a -> List a -> Type where
  PermNil : Perm [] []
  PermInsert : Perm r1 (l2 ++ r2) -> Perm (x :: r1) (l2 ++ x :: r2)

---+------------------------------------------
---+  PermCode and permute
---+------------------------------------------

data PermCode : Nat -> Type where
  PZ : PermCode Z
  PS : PermCode k -> Fin (S k) -> PermCode (S k)

Permute : PermCode n -> Vect n a -> Vect n a
Permute PZ [] = []
Permute (PS c i) (x :: xs) = let subv = Permute c xs in insertAt i x subv

---+------------------------------------------
---+  My definition of a permutation
---+------------------------------------------

{- Error in next (as expected) -- Type mismatch between
                             plus m (S n)  and
                             S (plus m n)

data VPerm : Vect n a -> Vect n a -> Type where
  VPermNil : VPerm [] []
  VPermInsert : VPerm r1 (l2 ++ r2) -> VPerm (x :: r1) (l2 ++ x :: r2)
-}

data VPerm : Vect n a -> Vect n a -> Type where
  VPermNil : VPerm [] []
  VPermInsert : VPerm {n=p} v1 v2 -> (i : Fin (S p)) -> VPerm (x :: v1) (insertAt i x v2)

---+------------------------------------------
---+  Generating permutations
---+------------------------------------------

flatmap : (a -> List b) -> List a -> List b
flatmap f [] = []
flatmap f (x :: xs) = (f x) ++ (flatmap f xs)

GenFins : (n : Nat) -> List (Fin n)
GenFins Z = []
GenFins (S k) = FZ :: map FS (GenFins k)

GenPerms : {n : Nat} -> (v1 : Vect n a) -> List (v2 ** VPerm v1 v2)
GenPerms {n = Z} [] = [([] ** VPermNil)]
GenPerms {n = (S k)} (x :: xs) = 
  let 
    recv = GenPerms {n = k} xs 
    stepf : ((v2 : Vect k a ** VPerm xs v2) -> List (v2' : Vect (S k) a ** VPerm (x :: xs) v2')) 
          = (\(v2 ** prf) => map (\i => (insertAt i x v2 ** VPermInsert prf i)) (GenFins $ S k))
  in flatmap stepf recv

---+------------------------------------------
---+  Showing that codes and VPerms relate
---+------------------------------------------

pcode2vperm : (c : PermCode n) -> (v1 : Vect n a) -> VPerm v1 (Permute c v1)
pcode2vperm PZ [] = VPermNil
pcode2vperm (PS c i) (x :: xs) = VPermInsert {x=x} (pcode2vperm c xs) i

vperm2pcode : VPerm {n} v1 v2 -> PermCode n
vperm2pcode VPermNil = PZ
vperm2pcode (VPermInsert vperm i) = PS (vperm2pcode vperm) i

lem_vperm2code_ok: (vperm : VPerm {n} v1 v2) -> v2 = Permute (vperm2pcode vperm) v1
lem_vperm2code_ok VPermNil = Refl
lem_vperm2code_ok (VPermInsert vperm i) = cong $ lem_vperm2code_ok vperm

lem_inv1 : (c : PermCode n) -> (v1 : Vect n a) -> (vperm2pcode (pcode2vperm c v1) = c)
lem_inv1 PZ [] = Refl
lem_inv1 (PS c i) (x :: xs) = cong {f = (\c => PS c i)} $ lem_inv1 c xs

{-
-- Stuck.  Incomplete.

-- I think the problem is that this lemma is proving an ill-formed equality.
-- The equality is `pcode2vperm (vperm2pcode vperm) v1 = vperm`
--   but pcode2vperm yields a value of type `VPerm v1 (Permute c v1)` 
--   while the type of vperm is `VPerm v1 v2`.
-- So while it appears that the ih is just what we need, it has this illformed equality and, so, can't be used.

-- OLDER:
-- TRY adding "{v1} {v2}" to equations and make sure right thing is passed for ih
-- maybe make at least v1 explicit
-- and maybe pass to inner vperm2pcode

lem_inv2 : (vperm : VPerm {n} v1 v2) -> (pcode2vperm (vperm2pcode vperm) v1 = vperm)
lem_inv2 VPermNil = Refl
lem_inv2 (VPermInsert {v1} {v2} vperm i) = 
  let 
    ih = lem_inv2 vperm 
    tlhs_ih = pcode2vperm (vperm2pcode vperm) v1
    vperm2 : (v2 = Permute (vperm2pcode vperm) v1) = lem_vperm2code_ok vperm
    vperm' : (VPerm v1 (Permute (vperm2pcode vperm) v1)) = rewrite (sym vperm2) in vperm
    --xxx = cong {f = (\vperm => vperm')} ih
    --xxx = cong {f = (\vperm => VPermInsert vperm i)} ih 
  in ?h -- -- ?lem_inv2_rhs_2
{-
    When checking right hand side of lem_inv2 with expected type
             pcode2vperm (vperm2pcode (VPermInsert vperm i)) (x :: v1) = VPermInsert vperm i
     
     When checking an application of function Prelude.Basics.cong:
             Type mismatch between
                     pcode2vperm (vperm2pcode vperm) v1 = vperm (Type of ih)
             and
                     pcode2vperm (vperm2pcode vperm) v1 = vperm (Expected type)
             
             Specifically:
                     Type mismatch between
                             Permute (vperm2pcode vperm) v1
                     and
                             v2

-}
-}

pcode2vperm' : (c : PermCode n) -> (v1 : Vect n a) -> (v2 : Vect n a ** (v2 = Permute c v1, VPerm v1 v2))
pcode2vperm' PZ [] = ([] ** (Refl, VPermNil))
pcode2vperm' (PS c i) (x :: xs) = 
  let 
    (rv2 ** (pv2, rperm)) = pcode2vperm' c xs
  in (insertAt i x rv2 ** (cong pv2, VPermInsert {x=x} rperm i))


{-
vperm2pcode : VPerm v1 v2 -> (c : PermCode n ** v2 = Permute c v1)
vperm2pcode VPermNil = (PZ ** Refl)
vperm2pcode (VPermInsert {v1} {v2} {x} vperm i) = 
  let 
    (c ** peq) = vperm2pcode vperm 
    xxx = PS c i
    yyy : (insertAt i x v2 = Permute (PS c i) (x :: v1)) = ?h
  in ((PS c i) ** yyy)
-}
