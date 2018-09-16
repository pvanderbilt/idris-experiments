module CatConstructions

import CatCore

%access public export
%default total


---+-----------------------------------------------
---+ Terminal and Initial Objects
---+-----------------------------------------------

-- IsTerminal {c} x is true when x is a terminal object of c
-- Proof is a pair (inArrow, uniq) where 
--    `inArrow y` is an arrow from y to x and 
--    `uniq y` says all such arrows are equal
IsTerminal : {c : Category} -> (x : Obj c) -> Type
IsTerminal {c} x = ((y : Obj c) -> Hom y x, {y : Obj c} -> IsUniqueHom y x)

-- IsInitial {c} x is true when x is an initial object of c
-- Proof is a pair (outArrow, uniq) where 
--    `outArrow y` is an arrow from x to y and 
--    `uniq y` says all such arrows are equal
IsInitial : {c : Category} -> (x : Obj c) -> Type
IsInitial {c} x = ((y : Obj c) -> Hom x y, {y : Obj c} -> IsUniqueHom x y)


---+-----------------------------------------------
---+ Properties of Terminal and Initial objects
---+-----------------------------------------------

-- Any two terminal objects are isomorphic
lem_TerminalsIso : {c : Category} -> (x, y : Obj c) -> IsTerminal x -> IsTerminal y -> IsomorphicObjs x y
lem_TerminalsIso {c} x y (xInArr, xUniqPrf) (yInArr, yUniqPrf) = 
  let
    f   : Hom {c=c} x y = yInArr x
    g   : Hom {c=c} y x = xInArr y
    xinv =  xUniqPrf (g . f) (id x)
    yinv =  yUniqPrf (f . g) (id y)
  in MkIsoObjPf f g xinv yinv
  
-- Any two such isomorphisms are isomorphic
lem_TermIsosIso : {c : Category} -> (x, y : Obj c) -> IsTerminal x -> IsTerminal y
                  -> (p, q : IsomorphicObjs x y) -> IsomorphicIsos p q
lem_TermIsosIso x y (xInArr, xUniqPrf) (yInArr, yUniqPrf) 
                p@(MkIsoObjPf f1 g1 _ _) q@(MkIsoObjPf f2 g2 _ _)
  = MkIsoIsoPf p q (yUniqPrf f1 f2, xUniqPrf g1 g2)

---+-----------------------------------------------
---+ Registering particular objects as
---+   Terminal or Initial
---+-----------------------------------------------

-- TheTerminalFor c x is true when x has been registered as "the" terminal object for c
-- A proof of `TheTerminalFor c` is a pair of an object and a proof that it's terminal
TheTerminalFor : (c : Category) -> Type
TheTerminalFor c = (x : Obj c ** IsTerminal x)

-- TerminalObj c yields the terminal object registered by above
TerminalObj : (c : Category) -> {auto prf : TheTerminalFor c} -> Obj c
TerminalObj c {prf = (x ** pf)} = x

TerminalObjPrf : (c : Category) -> {auto prf : TheTerminalFor c} -> IsTerminal (TerminalObj c)
TerminalObjPrf c {prf = (x ** pf)} = pf

{-
data ExU : (a : Type) -> (eq : a -> a -> Type) -> (p : a -> Type) -> Type where
  EUVal : (witness : a) -> (prf : p witness) -> (prfUniq : (other : a) -> (p other) -> (eq witness other)) -> ExU a eq p

record TerminalObjX (c : Category) where
  constructor MkTerminalObjX
  TerminalObj  : Obj c
  InArrow      : (x : Obj c) -> Hom x TerminalObj 
  InArrowUniq  : (x : Obj c) -> (a : Hom x TerminalObj) -> a = (InArrow x)

record InitialObjX (c : Category) where
  constructor MkInitialObjX
  InitialObj   : Obj c
  OutArrow     : (x : Obj c) -> Hom InitialObj x
  OutArrowUniq : (x : Obj c) -> (a : Hom InitialObj x) -> a = (OutArrow x)

data IsInitialObj : (c : Category) -> (InitialObj : Obj c) -> Type where
  MkIsInitialObj : 
    (OutArrow     : (x : Obj c) -> Hom io x) ->
    (OutArrowUniq : (x : Obj c) -> (a : Hom io x) -> a = (OutArrow x))
    -> IsInitialObj c io
-}

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
