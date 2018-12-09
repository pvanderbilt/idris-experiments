module CatOpAdd

import CatMath
import CatCore
import CatConstructions
import CatOps

%access public export
%default total


--------------------------------------------------------------------------------
-- Cat: The category of categories
--------------------------------------------------------------------------------


---+---------------------------------------------------
---+  Definition of functor equality
---+---------------------------------------------------

-- Definition that 2 functors' AMaps each map f to equal arrows
--      (but the arrows are in different Homs)

FunctorAMapFEq : {c, d : Category} -> (m,n : Functor c d) -> FunEx (OMap m) (OMap n) 
                     -> (x, y : Obj c) -> (f : IHom c x y) -> Type
FunctorAMapFEq {c} {d} m n pOMEq x y f = 
  let 
    mx = OMap m x
    my = OMap m y
    nx = OMap n x
    ny = OMap n y
    pex : (mx = nx) = pOMEq x
    pey : (my = ny) = pOMEq y
    am1 : IHom d mx my = IAMap m x y f
    am2 : IHom d nx ny = IAMap n x y f
    am2' : IHom d mx ny = rewrite pex in am2
    am2'' : IHom d mx my = rewrite pey in am2'
    p = (IAMap m x y f) = (IAMap n x y f)
  in am1 === am2''

-- Definition of functors' AMaps being equal

FunctorAMapsEq : {c, d : Category} -> (m,n : Functor c d) -> FunEx (OMap m) (OMap n) -> Type
FunctorAMapsEq {c} {d} m n pOMEq = (x, y : Obj c) -> (f : IHom c x y) -> FunctorAMapFEq m n pOMEq x y f

-- Definition of FunctorEq: Functors m and n are equal

FunctorEq : {c, d : Category} -> Functor c d -> Functor c d -> Type
FunctorEq m n = (pOMEq : FunEx (OMap m) (OMap n) ** FunctorAMapsEq m n pOMEq)
--FunctorEq m n = (pOMEq : FunEx (OMap m) (OMap n) ** (x, y : Obj c) -> (f : IHom c x y) -> Tmp m n pOMEq x y f)

--------------------------------------------------------------------------------
-- The category, Cat, of categories
--------------------------------------------------------------------------------

CatCat : Category
CatCat = IMkCategory 
  Category                              -- Obj = Category
  (\c,d => Functor c d)                 -- Hom c d = Functor c d
  (\c => FunctorId c)                   -- id c = FunctorId c
  (\_,_,_, g,f => FunctorComp g f)      -- g . f = FunctorComp g f
  (\_,_, f,g => FunctorEq f g)          -- f === g = FunctorEq f g
 
