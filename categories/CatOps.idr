module CatOps

import CatCore
import CatConstructions
-- import Categories -- this import causes errors!
-- import Data.List

%access public export
%default total


---+--------------------------------------
---+  Category === laws
---+--------------------------------------

{-
record CatArrEqAx (c : Category) where
  constructor MkCatArrEqAx
  LawAE_Refl   : {x, y : Obj c} -> (f : Hom x y) -> f === f
  LawAE_Sym    : {x, y : Obj c} -> (f, g : Hom {c=c} x y) -> f === g -> g === f
  LawAE_Trans  : {x, y : Obj c} -> (f, g, h : Hom {c=c} x y) -> f === g -> g === h -> f === h
-}

-- Definition of an equivalence relation

record IsEquivRel (a : Type) (r : a -> a -> Type) where
  constructor MkIsEquivRel
  Eq_refl  : (x : a) -> r x x
  Eq_sym   : (x, y : a) -> r x y -> r y x
  Eq_trans : (x, y, z : a) -> r x y -> r y z -> r x z

-- Proof that Id is an equivalence relation
IdIsEquiv : (a : Type) -> IsEquivRel a (=)
IdIsEquiv a = MkIsEquivRel (\_ => Refl) (\_,_ => sym) (\_,_,_ => trans)

-- Proof that FunEx is an equivalence relation
FunExIsEquiv : (a, b : Type) -> IsEquivRel (a -> b) FunEx
FunExIsEquiv a b = MkIsEquivRel 
                     (\f, x => Refl) 
                     (\f,g, p, x => sym (p x)) 
                     (\f,g,h, pfg, pgh, x => trans (pfg x) (pgh x))

-- Predicate saying that a category's arrow equality (===) is an equivalence relation
CatArrEqIsEquiv : (c : Category) -> Type
CatArrEqIsEquiv c = (x, y : Obj c) -> IsEquivRel (IHom c x y) (IArrowEq c x y)



--------------------------------------------------------------------------------
--------------------------------------------------------------------------------
-- Functors
--------------------------------------------------------------------------------
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

-- LemFunctorCompObjs

---+---------------------------------------------------
---+  Definition of Functor laws
---+---------------------------------------------------

record FunctorLaws (c : Category) (d : Category) (fcd : Functor c d) where
  constructor MkFunctorLaws
  LawF_eq   : (x, y : Obj c) -> (f, g : Hom x y) -> f === g -> AMap fcd f === AMap fcd g  -- functor preserves ===
  LawF_id   : (x : Obj c) -> AMap fcd (id x) === id (OMap fcd x)                          -- functor preserves id
  LawF_Comp : (x, y, z : Obj c) -> (g : Hom y z) -> (f : Hom x y) ->                      -- functor preserves comp
                 AMap fcd (g . f) === (AMap fcd g) . (AMap fcd f)

-- Proof that FunctorId is a functor
FunctorIdIsaFunctor : (c : Category) -> CatArrEqIsEquiv c -> FunctorLaws c c (FunctorId c)
FunctorIdIsaFunctor c ceqax = MkFunctorLaws 
                          (\_, _, f, g, pfgeq => pfgeq)                    -- LawF_eq
                          (\x => (Eq_refl (ceqax x x) (id x)))             -- LawF_id
                          (\_,_,_, g, f => (Eq_refl (ceqax _ _) (g . f)))  -- LawF_comp

-- Proof that FunctorComp yields a functor
FunctorCompEqOK : {c, d, e : Category} -> (fde : Functor d e) -> (fcd : Functor c d) -> 
                                (fcdFPrf : FunctorLaws c d fcd) -> (fdeFPrf : FunctorLaws d e fde) ->
                                (x, y : Obj c) -> (f, g : Hom x y) -> f === g -> 
                                IAMap (FunctorComp fde fcd) _ _ f === IAMap (FunctorComp fde fcd) _ _ g
FunctorCompEqOK fde fcd fcdFPrf fdeFPrf x y f g pfgeq = 
  let 
    pcd = LawF_eq fcdFPrf x y f g pfgeq 
    pde = LawF_eq fdeFPrf (OMap fcd x) (OMap fcd y) (IAMap fcd x y f) (IAMap fcd x y g) pcd
  in pde

-- ID OK
FunctorCompIdOK : {c, d, e : Category} -> (fde : Functor d e) -> (fcd : Functor c d) -> 
                                (pFLcd : FunctorLaws c d fcd) -> (pFLde : FunctorLaws d e fde) ->
                                (pEEqEquiv : CatArrEqIsEquiv e) ->
                                let fce : Functor c e = FunctorComp fde fcd in
                                (x : Obj c) -> IAMap fce x x (IId c x) === IId e (OMap fce x)
FunctorCompIdOK {c=c} {d=d} {e=e} fde fcd pFLcd pFLde pEEqEquiv x  = 
  let
    mx = OMap fcd x
    mmx = OMap fde mx
    idc = IId c x
    idd = IId d mx
    ide = IId e mmx
    midc : IHom d mx mx = IAMap fcd x x idc
    midd : IHom e mmx mmx = IAMap fde mx mx idd
    mmidc : IHom e mmx mmx = IAMap fde mx mx midc
    -- peqd : ((===) {c=d} {x=mx} {y=mx} midc idd) = LawF_id pFLcd x                           -- : midc === idd (in d)
    -- peqe : ((===) {c=e} {x=mmx} {y=mmx} midd ide) = LawF_id pFLde mx                        -- : midd === ide (in e)
    -- epeqd : ((===) {c=e} {x=mmx} {y=mmx} mmidc midd) = LawF_eq pFLde mx mx midc idd peqd    -- : mmidc === midd (in e)
    peqd = LawF_id pFLcd x                                      -- : midc === idd (in d)
    peqe = LawF_id pFLde mx                                     -- : midd === ide (in e)
    epeqd = LawF_eq pFLde mx mx midc idd peqd                   -- : mmidc === midd (in e)
    p = Eq_trans (pEEqEquiv mmx mmx) mmidc midd ide epeqd peqe  -- : mmidc === ide (in e)
  in p

-- Comp OK
FunctorCompCompOK : {c, d, e : Category} -> (fde : Functor d e) -> (fcd : Functor c d) -> 
                                (pFLcd : FunctorLaws c d fcd) -> (pFLde : FunctorLaws d e fde) ->
                                (pEEqEquiv : CatArrEqIsEquiv e) ->
                                let fce : Functor c e = FunctorComp fde fcd in
                                (x, y, z : Obj c) -> (g : Hom y z) -> (f : Hom x y) -> (AMap fce (g . f)) === (AMap fce g) . (AMap fce f)

FunctorCompCompOK {c=c} {d=d} {e=e} fde fcd pFLcd pFLde pEEqEquiv x y z g f = 
  let
    -- cat c
    cgf = g . f
    -- cat d
    mx : Obj d = OMap fcd x
    my : Obj d = OMap fcd y
    mz : Obj d = OMap fcd z
    mg : IHom d my mz = IAMap fcd y z g
    mf : IHom d mx my = IAMap fcd x y f
    mcgf : IHom d mx mz = IAMap fcd x z cgf
    cmgmf : IHom d mx mz = mg . mf
    -- cat e
    mmx = OMap fde mx
    mmy = OMap fde my
    mmz = OMap fde mz
    mmg : IHom e mmy mmz = IAMap fde my mz mg
    mmf : IHom e mmx mmy = IAMap fde mx my mf
    mmcgf : IHom e mmx mmz = IAMap fde mx mz mcgf
    mcmgmf : IHom e mmx mmz = IAMap fde mx mz cmgmf
    cmmgmmf : IHom e mmx mmz = mmg . mmf
    -- equalities
    r1 : (mcgf === cmgmf) = LawF_Comp pFLcd x y z g f                 -- m (g.f) = mg . mf
    pr1 : (mmcgf === mcmgmf) = LawF_eq pFLde mx mz mcgf cmgmf r1      -- mm (g.f) = m (mg . mf)
    r2 : (mcmgmf === cmmgmmf) = LawF_Comp pFLde mx my mz mg mf        -- m (mg . mf) = mmg . mmf
    p = Eq_trans (pEEqEquiv mmx mmz) mmcgf mcmgmf cmmgmmf pr1 r2      -- mm (g.f) = mmg . mmf
  in p


FunctorCompYieldsaFunctor : {c, d, e : Category} -> (fde : Functor d e) -> (fcd : Functor c d) -> 
                                (pFLcd : FunctorLaws c d fcd) -> (pFLde : FunctorLaws d e fde) ->
                                (pEEqEquiv : CatArrEqIsEquiv e) ->
                                FunctorLaws c e (FunctorComp fde fcd)
FunctorCompYieldsaFunctor {c=c} {d=d} {e=e} fde fcd pFLcd pFLde pEEqEquiv = MkFunctorLaws 
    (FunctorCompEqOK fde fcd pFLcd pFLde) 
    (FunctorCompIdOK fde fcd pFLcd pFLde pEEqEquiv)
    (FunctorCompCompOK fde fcd pFLcd pFLde pEEqEquiv)

{-                                
FunctorCompYieldsaFunctor c ceqax = MkFunctorLaws 
                          (\f, g, pfgeq => pfgeq)             -- LawF_eq
                          (\x => (Eq_refl ceqax (id x)))      -- LawF_id
                          (\g, f => (Eq_refl ceqax (g . f)))  -- LawF_comp

-}
