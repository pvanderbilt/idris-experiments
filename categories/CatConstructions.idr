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
