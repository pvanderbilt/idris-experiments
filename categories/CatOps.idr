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



--------------------------------------------------------------------------------
-- Product of Categories
--    (Different from the internal prod construction)
--------------------------------------------------------------------------------

---+---------------------------------------------------
---+  ProdCat: The cartesian product of two categories
---+---------------------------------------------------

PCObj : (c1, c2 : Category) -> Type
PCObj c1 c2 = (Obj c1, Obj c2) 

PCHom : (c1, c2 : Category) -> (x, y : PCObj c1 c2) -> Type
PCHom c1 c2 = (\(x1, x2), (y1, y2) => (IHom c1 x1 y1, IHom c2 x2 y2))

PCId : (c1, c2 : Category) -> (x : PCObj c1 c2) -> PCHom c1 c2 x x
PCId c1 c2 = (\(x1, x2) => (IId c1 x1 , IId c2 x2))

PCComp : (c1, c2 : Category) -> (x, y, z : PCObj c1 c2) 
         -> PCHom c1 c2 y z -> PCHom c1 c2 x y -> PCHom c1 c2 x z
PCComp c1 c2 = (\(x1, x2), (y1, y2), (z1, z2), (g1, g2), (f1, f2) 
               => (IComp c1 x1 y1 z1 g1 f1 , IComp c2 x2 y2 z2 g2 f2))

PCIArrowEq : (c1, c2 : Category) -> (x, y : PCObj c1 c2) 
             -> (f, g : PCHom c1 c2 x y) -> Type
PCIArrowEq c1 c2 = (\(x1, x2), (y1, y2), (g1, g2), (f1, f2)  
                   => (IArrowEq c1 x1 y1 g1 f1 , IArrowEq c2 x2 y2 g2 f2))

ProdCat: Category -> Category -> Category
ProdCat c1 c2 = IMkCategory (PCObj c1 c2) (PCHom c1 c2) (PCId c1 c2) (PCComp c1 c2) (PCIArrowEq c1 c2)


--------------------------------------------------------------------------------
-- Bifunctor : c1 x c2 --> d
--------------------------------------------------------------------------------

BiFunctor : (c1, c2 : Category) -> Category -> Type
BiFunctor c1 c2 d = Functor (ProdCat c1 c2) d

EndoBiFunctor : Category -> Type
EndoBiFunctor c = BiFunctor c c c
