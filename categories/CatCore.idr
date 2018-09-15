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
  Obj     : Type
  IHom    : (x, y : Obj) -> Type
  IId     : (x : Obj) -> IHom x x
  IComp   : {x, y, z : Obj} -> (g : IHom y z) -> (f : IHom x y) -> IHom x z
  ArrowEq : {x, y : Obj} -> (f, g : IHom x y) -> Type
  

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
(===) {c} f g = ArrowEq c f g


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

