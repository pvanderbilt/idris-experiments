module CatMath

%access public export
%default total


--------------------------------------------------------------------------------
--------------------------------------------------------------------------------
-- Some basic math used in category theory
--------------------------------------------------------------------------------
--------------------------------------------------------------------------------

--------------------------------------------------------------------------------
-- Equality relations
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
---+ Definition of an equivalence relation
---+-----------------------------------------------


record IsEquivRel (a : Type) (r : a -> a -> Type) where
  constructor MkIsEquivRel
  Eq_refl  : (x : a) -> r x x
  Eq_sym   : (x, y : a) -> r x y -> r y x
  Eq_trans : (x, y, z : a) -> r x y -> r y z -> r x z

-- Proof that Id is an equivalence relation
IdIsEquiv : (a : Type) -> IsEquivRel a (\x,y => x=y)
IdIsEquiv a = MkIsEquivRel (\_ => Refl) (\_,_ => sym) (\_,_,_ => trans)

-- Proof that FunEx is an equivalence relation
FunExIsEquiv : (a, b : Type) -> IsEquivRel (a -> b) FunEx
FunExIsEquiv a b = MkIsEquivRel 
                     (\f, x => Refl) 
                     (\f,g, p, x => sym (p x)) 
                     (\f,g,h, pfg, pgh, x => trans (pfg x) (pgh x))

-- Proof that FlatEq is an equivalence relation
FlatEqIsEquiv :  (a : Type) -> IsEquivRel a (\x,y => FlatEq x y)
FlatEqIsEquiv a = MkIsEquivRel 
                     (\f => TheyBEq f f) 
                     (\f,g, p => TheyBEq g f) 
                     (\f,g,h, pfg, pgh => TheyBEq f h)

---+-----------------------------------------------
---+ Proof that xa=ya & xb=yb implies f xa xb = f ya yb
---+-----------------------------------------------

ap2 : {a, b, c : Type} -> (f : a -> b -> c) -> {xa, ya : a} -> {xb, yb : b}  
      -> xa = ya -> xb = yb -> f xa xb = f ya yb
ap2 f Refl Refl = Refl
