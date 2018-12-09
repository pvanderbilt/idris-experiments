module CatOps

import CatMath
import CatCore
import CatConstructions
-- import Categories -- not used

%access public export
%default total


--------------------------------------------------------------------------------
--------------------------------------------------------------------------------
-- Operations on or between categories (so external)
--------------------------------------------------------------------------------
--------------------------------------------------------------------------------


--------------------------------------------------------------------------------
-- Functions on categories
--------------------------------------------------------------------------------

---+---------------------------------------------------
---+ OpCat: The category in which all arrows are reversed.
---+---------------------------------------------------

OpCat: Category -> Category
OpCat c = IMkCategory
  (Obj c)                             -- Obj = Obj c
  (\x,y => IHom c y x)                -- Hom x y = Hom {c} y x
  (IId c)                             -- id = id
  (\x,y,z, g,f => IComp c z y x f g)  -- g . f = f .{c} g
  (\x,y, f,g => IArrowEq c y x f g)   -- (===) = (===) {c}


OpCatAx: (c: Category) -> CategoryAx c -> CategoryAx (OpCat c)
OpCatAx c cax = 
  let 
    pEqAx = Law_arrEqIsEquiv cax
  in MkCatAx 
    (Law_idL cax)                     -- Law_idR f : f === f . (id x)
    (Law_idR cax)                     -- Law_idL f : f === (id y) . f
    (\f,g,h => Eq_sym (pEqAx _ _) _ _ -- Law_assoc f g h : ((h . g) . f) === (h . (g . f))
      (Law_assoc cax h g f))
    (\x,y => let p = pEqAx y x        -- Law_arrEqIsEquiv x y : IsEquivRel (IHom c x y) (IArrowEq c x y)
             in MkIsEquivRel (Eq_refl p) (Eq_sym p) (Eq_trans p))



--------------------------------------------------------------------------------
-- Functors
--------------------------------------------------------------------------------

---+---------------------------------------------------
---+  Definition of a Functor
---+---------------------------------------------------

record Functor (c : Category) (d : Category) where
  constructor MkFunctor
  OMap : (Obj c) -> (Obj d)
  IAMap : (x, y : Obj c) -> IHom c x y -> IHom d (OMap x) (OMap y)

AMap : (fcd : Functor c d) -> {x, y : Obj c} -> IHom c x y -> IHom d (OMap fcd x) (OMap fcd y)
AMap fcd {x} {y} f = IAMap fcd x y f

---+---------------------------------------------------
---+  Definition of an EndoFunctor
---+---------------------------------------------------

EndoFunctor : Category -> Type
EndoFunctor c = Functor c c

---+---------------------------------------------------
---+  Definitions of functor identity and composition
---+---------------------------------------------------
FunctorId : (c : Category) -> Functor c c
FunctorId c = MkFunctor id (\_,_ => id)

FunctorComp : {c, d, e : Category} -> (fde : Functor d e) -> (fcd : Functor c d) -> Functor c e
FunctorComp {c=c} fde fcd = MkFunctor ((OMap fde) . (OMap fcd)) (\x,y, f => (IAMap fde _ _ (IAMap fcd x y f))) 

---+---------------------------------------------------
---+  Definition of Functor laws
---+---------------------------------------------------

record FunctorLaws (c : Category) (d : Category) (fcd : Functor c d) where
  constructor MkFunctorLaws
  LawF_eq   : (x, y : Obj c) -> (f, g : Hom x y) -> f === g -> AMap fcd f === AMap fcd g  -- functor preserves ===
  LawF_id   : (x : Obj c) -> AMap fcd (id x) === id (OMap fcd x)                          -- functor preserves id
  LawF_Comp : (x, y, z : Obj c) -> (g : Hom y z) -> (f : Hom x y) ->                      -- functor preserves comp
                 AMap fcd (g . f) === (AMap fcd g) . (AMap fcd f)

EndoFunctorLaws : (c : Category) -> (F : Functor c c) -> Type
EndoFunctorLaws c fF = FunctorLaws c c fF
