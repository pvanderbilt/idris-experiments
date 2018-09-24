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
  Comp     : (f, g : Arrow) -> {auto peq : Cod g = Dom f} -> Arrow
  CompProp : (f, g, fog : Arrow) -> (peq : Cod g = Dom f) -> (fog = Comp f g {peq=peq}) 
             -> (Dom fog = Dom g , Cod fog = Cod f)


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
  (\hf, hg => let 
                (f ** (pfd , pfc)) = hf
                (g ** (pgd , pgc)) = hg
                peq = trans pgc (sym pfd)
                fog = Comp ac f g {peq=peq}
                (pcd , pcc) = CompProp ac f g fog peq Refl
                (pfogd , pfogc) = (trans pcd pgd , trans pcc pfc)
              in (fog ** (pfogd , pfogc)) )
  (=)

{- alternate ending (GOOD)                              
                fogProp = CompProp ac f g fog peq Refl
              in rewrite (sym pgd) 
              in rewrite (sym pfc) 
              in (fog ** fogProp) )
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

R2A_Comp : {c : Category} -> (f, g : R2A_Arrow c) -> {auto peq :  R2A_Cod g =  R2A_Dom f} ->  R2A_Arrow c
R2A_Comp f g {peq} = let (fd ** (fc ** fa)) = f in 
                     let (gd ** gc ** ga) = g in 
                     let Refl = peq in 
                     (gd ** fc ** (fa . ga))

R2A_CompProp : {c : Category} -> (f, g, fog : R2A_Arrow c) -> (peq : R2A_Cod g = R2A_Dom f)
                  -> (fog = R2A_Comp f g {peq=peq}) -> (R2A_Dom fog = R2A_Dom g , R2A_Cod fog = R2A_Cod f)
R2A_CompProp f g fog peq prf = 
  let (fd ** (fc ** fa)) = f in 
  let (gd ** gc ** ga) = g in 
  let Refl = peq in 
    (cong {f = fst} prf, cong {f = (\fog => DPair.fst (DPair.snd fog))} prf)

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
  -- Comp     : (f, g : Arrow) -> {auto peq : Cod g = Dom f} -> Arrow
  (\f, g, peq => ((fst g) ** (fst $ snd f) ** IComp c (snd $ snd f) (snd $ snd g)))
    -- let (fd ** (fc ** fa)) = f in let (gd ** gc ** ga) = g in 
  -- CompProp : (f, g, fog : Arrow) -> (peq : Cod g = Dom f) -> (fog = Comp f g {peq=peq}) -> (Dom fog = Dom g , Cod fog = Cod f)
  ?hcp

-}
