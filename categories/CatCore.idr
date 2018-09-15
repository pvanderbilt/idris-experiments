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
  Hom     : (x, y : Obj) -> Type
  Id      : (x : Obj) -> Hom x x
  Comp    : {x, y, z : Obj} -> (g : Hom y z) -> (f : Hom x y) -> Hom x z
  ArrowEq : {x, y : Obj} -> (f, g : Hom x y) -> Type
  
-- Comp g f is "g after f"

-- g . f is Comp g f (is "g after f")
-- f >>> g  is "f then g"

infixr 1 >>>
(>>>) : {c : Category} -> {x, y, z : Obj c} -> Hom c x y -> Hom c y z -> Hom c x z
(>>>) {c} {x} {y} {z} f g = Comp c g f

(.) : {c : Category} -> {x, y, z : Obj c} -> Hom c y z -> Hom c x y -> Hom c x z
(.) {c} {x} {y} {z} g f = Comp c g f

---+--------------------------------------
---+  Category axioms
---+--------------------------------------

record CategoryAx (c : Category) where
  constructor MkCatAx
  Law_idR   : {x, y : Obj c} -> (f : Hom c x y) -> ArrowEq c f (Comp c f (Id c x))
  Law_idL   : {x, y : Obj c} -> (f : Hom c x y) -> ArrowEq c f (Comp c (Id c y) f)
  Law_assoc : {x, y, z, w : Obj c} -> (f : Hom c x y) -> (g : Hom c y z) -> (h : Hom c z w) 
              -> ArrowEq c (Comp c (Comp c h g) f) (Comp c h (Comp c g f))

---+----------------------------------------------
---+  Category Axioms with built-in = 
---+----------------------------------------------

record CategoryAxEq (c : Category) where
  constructor MkCatAxEq
  Law_idR   : {x, y : Obj c} -> (f : Hom c x y) -> f = (Comp c f (Id c x))
  Law_idL   : {x, y : Obj c} -> (f : Hom c x y) -> f = (Comp c (Id c y) f)
  Law_assoc : {x, y, z, w : Obj c} -> (f : Hom c x y) -> (g : Hom c y z) -> (h : Hom c z w) 
              -> (Comp c (Comp c h g) f) = (Comp c h (Comp c g f))

--------------------------------------------------------------------------------
-- Some useful functions
--------------------------------------------------------------------------------

---+-----------------------------------------------
---+ FunEx: Function extensionality
---+-----------------------------------------------

FunEx : (f,g : a->b) -> Type
FunEx f g = (x : _) -> (f x) = (g x)

