module ArrowCat

import CatCore

--------------------------------------------------------------------------------
-- A Category based on arrows and its mapping
--   However, I now think this is misguided because there isn't necessarily
--   object equality for categories.  I think Dom should be more like
--      Dom : Arrow -> Obj -> Type
--   and so on.
--------------------------------------------------------------------------------

---+--------------------------------------
---+  ArrowCategory
---+--------------------------------------

record ArrowCategory where
  constructor MkArrowCategory
  Obj      : Type
  Arrow    : Type
  Dom      : Arrow -> Obj
  Cod      : Arrow -> Obj
  Id       : (x : Obj) -> Arrow
  IdProp   : (x : Obj) -> (Dom (Id x) = x , Cod (Id x) = x)
  Comp     : (g, f : Arrow) -> {auto peq : Cod f = Dom g} -> Arrow
  CompProp : (g, f, gof : Arrow) -> (peq : Cod f = Dom g) -> (gof = Comp g f {peq=peq}) 
             -> (Dom gof = Dom f , Cod gof = Cod g)


---+------------------------------------------------------
---+  Mapping the arrow category to a regular one
---+    where an element of Hom x y is an arrow paired with 
---+    proofs that its dom is x and cod is y.
---+------------------------------------------------------

Arrow2Reg : ArrowCategory -> Category
Arrow2Reg ac = MkCategory 
  (Obj ac) 
  (\x,y => (a : Arrow ac ** (Dom ac a = x , Cod ac a = y)))
  (\x => (Id ac x ** IdProp ac x))
  (\hg, hf => let 
                (g ** (pgd , pgc)) = hg
                (f ** (pfd , pfc)) = hf
                peq = trans pfc (sym pgd)
                gof = Comp ac g f {peq=peq}
                (pcd , pcc) = CompProp ac g f gof peq Refl
                (pgofd , pgofc) = (trans pcd pfd , trans pcc pgc)
              in (gof ** (pgofd , pgofc)) )
  (=)

{- alternate ending (GOOD)                              
                gofProp = CompProp ac g f gof peq Refl
              in rewrite (sym pfd) 
              in rewrite (sym pgc) 
              in (gof ** gofProp) )
-}

---+------------------------------------------------------------
---+  Mapping the regular category to an arrow one
---+    where arrows are triples of the form (x, y, a : Hom x y)
---+------------------------------------------------------------

R2A_Obj : Category -> Type
R2A_Obj c = Obj c

R2A_Arrow : Category -> Type
R2A_Arrow c = (x : Obj c ** y : Obj c ** IHom c x y)

R2A_Dom : {c : Category} -> R2A_Arrow c -> R2A_Obj c
R2A_Dom a = fst a

R2A_Cod : {c : Category} -> R2A_Arrow c -> R2A_Obj c
R2A_Cod a = fst $ snd a

R2A_Id : {c : Category} -> R2A_Obj c -> R2A_Arrow c
R2A_Id x = (x ** x ** id x)

R2A_IdProp : {c : Category} -> (x : R2A_Obj c) -> (R2A_Dom (R2A_Id x) = x, R2A_Cod (R2A_Id x) = x)
R2A_IdProp x = (Refl, Refl)

R2A_Comp : {c : Category} -> (g, f : R2A_Arrow c) -> {auto peq :  R2A_Cod f =  R2A_Dom g} ->  R2A_Arrow c
R2A_Comp g f {peq} = let (gd ** (gc ** ga)) = g in 
                     let (fd ** fc ** fa) = f in 
                     let Refl = peq in 
                     (fd ** gc ** (ga . fa))

R2A_CompProp : {c : Category} -> (g, f, gof : R2A_Arrow c) -> (peq : R2A_Cod f = R2A_Dom g)
                  -> (gof = R2A_Comp g f {peq=peq}) -> (R2A_Dom gof = R2A_Dom f , R2A_Cod gof = R2A_Cod g)
R2A_CompProp g f gof peq prf = 
  let (gd ** (gc ** ga)) = g in 
  let (fd ** fc ** fa) = f in 
  let Refl = peq in 
    (cong {f = fst} prf, cong {f = (\gof => DPair.fst (DPair.snd gof))} prf)

Reg2Arrow : Category -> ArrowCategory
Reg2Arrow c = MkArrowCategory (R2A_Obj c) (R2A_Arrow c) R2A_Dom R2A_Cod R2A_Id R2A_IdProp R2A_Comp R2A_CompProp

{-  The error messages when doing it this way were too confusing,
    so changed to above.
Reg2Arrow c = MkArrowCategory
  -- Obj      : Type
  (Obj c)
  -- Arrow    : Type
  (x : Obj c ** y : Obj c ** Hom {c=c} x y)
  -- Dom      : Arrow -> Obj
  (\a => fst a) -- (\a => let (x ** y ** h) = a in x)
  -- Cod      : Arrow -> Obj
  (\a => fst $ snd a) -- ?y -- (\a => let (x ** y ** h) = a in y)
  -- Id       : (x : Obj) -> Arrow
  (\x => (x ** x ** Category.IId c x))
  -- IdProp   : (x : Obj) -> (Dom (Id x) = x , Cod (Id x) = x)
  (\x => (Refl, Refl))
  -- Comp     : (g, f : Arrow) -> {auto peq : Cod f = Dom g} -> Arrow
  (\g, f, peq => ((fst f) ** (fst $ snd g) ** IComp c (snd $ snd g) (snd $ snd f)))
    -- let (gd ** (gc ** ga)) = g in let (fd ** fc ** fa) = f in 
  -- CompProp : (g, f, gof : Arrow) -> (peq : Cod f = Dom g) -> (gof = Comp g f {peq=peq}) -> (Dom gof = Dom f , Cod gof = Cod g)
  ?hcp

-}
