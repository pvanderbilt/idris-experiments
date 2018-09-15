module CatConstructions

import CatCore

%access public export
%default total

data ExU : (a : Type) -> (eq : a -> a -> Type) -> (p : a -> Type) -> Type where
  EUVal : (witness : a) -> (prf : p witness) -> (prfUniq : (other : a) -> (p other) -> (eq witness other)) -> ExU a eq p

record TerminalObjX (c : Category) where
  constructor MkTerminalObjX
  TerminalObj  : Obj c
  InArrow      : (x : Obj c) -> Hom c x TerminalObj 
  InArrowUniq  : (x : Obj c) -> (a : Hom c x TerminalObj) -> a = (InArrow x)

record InitialObjX (c : Category) where
  constructor MkInitialObjX
  InitialObj   : Obj c
  OutArrow     : (x : Obj c) -> Hom c InitialObj x
  OutArrowUniq : (x : Obj c) -> (a : Hom c InitialObj x) -> a = (OutArrow x)

data IsInitialObj : (c : Category) -> (InitialObj : Obj c) -> Type where
  MkIsInitialObj : 
    (OutArrow     : (x : Obj c) -> Hom c io x) ->
    (OutArrowUniq : (x : Obj c) -> (a : Hom c io x) -> a = (OutArrow x))
    -> IsInitialObj c io

{- Thoughts:
  Define IsAnInitial as above, except category is implicit and Eq comes from there.
  Define InitialObj as a prop, such that one can assert that a particular obj is "the" initial obj of the cat.
  Show isomorphism between any two objects satisfying IsAnInitial -- define it.
    Define `Isomorphism x y` to be a structure with f,g and proofs
    Define InitialIso to take any two initial objects to an isomorphism
  Show that the isomorhism is unique.
  See paper notes around 18-09-10 and OO file.
-}

{-

---+-----------------------------------------------
---+ Initial and Terminal Objects for PLTypes (TBD)
---+-----------------------------------------------

testLemma: (a : Type) -> (f : Void -> a) -> (x : Void) -> f x = absurd x
testLemma a f x impossible

{- Need FunEx for this, but needs to be allowed by the definition. 
ioPrf : IsInitialObj PLTypeCat Void
ioPrf = let
          outArr : ((a : Type) -> Void -> a) = (\_ => void)
          outArrsUniq : ((a : Type) -> (f : Void -> a) -> f = void) = ?h2
        in MkIsInitialObj outArr outArrsUniq
-}

after : (g : b->c) -> (f : a -> b) -> (a -> c)
after g f = (g . f)

-}
