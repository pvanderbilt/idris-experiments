module CatCore

%access public export
%default total


--------------------------------------------------------------------------------
-- Categories
--------------------------------------------------------------------------------

---+--------------------------------------
---+  The basic Category record type
---+--------------------------------------

record Category where
  constructor MkCategory
  Obj      : Type
  IHom     : (x, y : Obj) -> Type
  IId      : (x : Obj) -> IHom x x
  IComp    : {x, y, z : Obj} -> (g : IHom y z) -> (f : IHom x y) -> IHom x z
  IArrowEq : {x, y : Obj} -> (f, g : IHom x y) -> Type
  

-- ACCESSORS

-- Homomorphisms of c from x to y

Hom : {c : Category} -> (x, y : Obj c) -> Type
Hom {c} x y = IHom c x y

-- The identity function of c

id : {c : Category} -> (x : Obj c) -> Hom x x
id {c} x = IId c x

-- Composition in c: `g . f` is "g after f"

(.) : {c : Category} -> {x, y, z : Obj c} -> IHom c y z -> IHom c x y -> IHom c x z
(.) {c} g f = IComp c g f

-- Arrow equality in c: `f === g` means that c has that f and g are the same arrow 
infixr 1 ===
(===) : {c : Category} -> {x, y : Obj c} -> (f, g : IHom c x y) -> Type
(===) {c} f g = IArrowEq c f g


---+--------------------------------------
---+  Category axioms
---+--------------------------------------

record CategoryAx (c : Category) where
  constructor MkCatAx
  Law_idR   : {x, y : Obj c} -> (f : Hom x y) -> f === f . (id x)
  Law_idL   : {x, y : Obj c} -> (f : Hom x y) -> f === (id y) . f
  Law_assoc : {x, y, z, w : Obj c} -> (f : Hom x y) -> (g : Hom y z) -> (h : Hom z w) 
                ->  (.) {c=c} (h . g) f === h . (g . f)

{- Had trouble with getting the wrong implicit c, so made it explicit in the last line. -}

---+----------------------------------------------
---+  Category Axioms with built-in = 
---+----------------------------------------------

record CategoryAxEq (c : Category) where
  constructor MkCatAxEq
  Law_idR   : {x, y : Obj c} -> (f : Hom x y) -> f = (IComp c f (id x))
  Law_idL   : {x, y : Obj c} -> (f : Hom x y) -> f = (IComp c (id y) f)
  Law_assoc : {x, y, z, w : Obj c} -> (f : Hom x y) -> (g : Hom y z) -> (h : Hom z w) 
              -> (IComp c ((.) h g) f) = (IComp c h (CatCore.(.) g f))
  CheckEq   : {x, y : Obj c} -> (f, g : IHom c x y) -> (IArrowEq c f g) = (f = g)

{-  Had trouble with (.) being interpreted as from Prelude.Basics (because (=) is heterogeneous),
    so changed to explicit `IComp c` -}

--------------------------------------------------------------------------------
-- Some useful functions
--------------------------------------------------------------------------------

---+-----------------------------------------------
---+ FunEx: Function extensionality
---+-----------------------------------------------

FunEx : (f,g : a->b) -> Type
FunEx f g = (x : _) -> (f x) = (g x)


---+-----------------------------------------------
---+ FlatEq: Equality where all instances are equal
---+-----------------------------------------------

data FlatEq : {a : Type} -> (f, g : a) -> Type where
  TheyBEq :  {a : Type} -> (f, g : a) -> FlatEq f g


---+-----------------------------------------------
---+ Uniqueness and singleton
---+-----------------------------------------------

IsUniqueArr : {c : Category} -> {x, y : Obj c} -> (f : Hom x y) -> Type
IsUniqueArr {x} {y} f = (g : Hom x y) -> f === g

IsSingletonHom : {c : Category} -> (x, y : Obj c) -> Type
IsSingletonHom x y = (f : Hom x y ** IsUniqueArr f)

-- Any two arrows are equal
IsUniqueHom : {c : Category} -> (x, y : Obj c) -> Type
IsUniqueHom x y = (f, g : Hom x y) -> f === g

IsSingletonHom' : {c : Category} -> (x, y : Obj c) -> Type
IsSingletonHom' x y = (Hom x y, IsUniqueHom x y)

IsThinCat : (c : Category) -> Type
IsThinCat c = (x, y : Obj c) -> IsUniqueHom x y

---+-----------------------------------------------
---+ Object Isomorphism
---+-----------------------------------------------

data IsomorphicObjs : {c : Category} -> (x, y : Obj c) -> Type where
  MkIsoObjPf : {x, y : Obj c} -> (f : Hom x y) -> (g : Hom y x) -> 
    (pgf : g . f === id x) -> (pfg : f . g === id y) 
    -> IsomorphicObjs x y


data IsomorphicIsos : {c : Category} -> {x, y : Obj c} -> (p, q : IsomorphicObjs x y) -> Type where
  MkIsoIsoPf : {x, y : Obj c} -> (p1, p2 : IsomorphicObjs x y) 
    -> (let (MkIsoObjPf f1 g1 _ _) = p1 in let (MkIsoObjPf f2 g2 _ _) = p2 in (f1 === f2, g1 === g2))
    -> IsomorphicIsos p1 p2

{- Note: records with implicit parameters don't work well -}
