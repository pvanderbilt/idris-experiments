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
  CompProp : (f, g, fog : Arrow) -> (peq : Cod g = Dom f) -> (fog = Comp f g {peq=peq}) -> (Dom fog = Dom g , Cod fog = Cod f)


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


---+------------------------------------------------------------
---+  Mapping the regular category to an arrow one
---+    where arrows are triples of the form (x, y, a : Hom x y)
---+------------------------------------------------------------

{- -- NOT FINISHED
Reg2Arrow : Category -> ArrowCategory
Reg2Arrow c = MkArrowCategory
  -- Obj      : Type
  (Obj c)
  -- Arrow    : Type
  (x : Obj c ** y : Obj c ** Hom c x y)
  -- Dom      : Arrow -> Obj
  (\a => let (x ** y ** h) = a in x)
  -- Cod      : Arrow -> Obj
  ?c -- (\(_ ** y ** _) => y)
  -- Id       : (x : Obj) -> Arrow
  ?id -- (\x => (x ** x ** Id c x))
  -- IdProp   : (x : Obj) -> (Dom (Id x) = x , Cod (Id x) = x)
  ?idp -- (\x => (Refl, Refl))
  -- Comp     : (f, g : Arrow) -> {auto peq : Cod g = Dom f} -> Arrow
  ?hc -- (\f, g, peq => let ((fd, fc) ** fa) = f in let ((gd, gc) ** ga) = g in ((gd, fc) ** Comp c fa ga))
  -- CompProp : (f, g, fog : Arrow) -> (peq : Cod g = Dom f) -> (fog = Comp f g {peq=peq}) -> (Dom fog = Dom g , Cod fog = Cod f)
  ?hcp

-}
-}
