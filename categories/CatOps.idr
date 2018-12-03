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
---+  Definition of OpCat which yields 
---+ the opposite category (one with arrows reversed)
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
FunctorIdIsaFunctor : (c : Category) -> CategoryAx c -> FunctorLaws c c (FunctorId c)
FunctorIdIsaFunctor c cax = 
  let ceqax = (Law_arrEqIsEquiv cax) in MkFunctorLaws 
                          (\_, _, f, g, pfgeq => pfgeq)                    -- LawF_eq
                          (\x => (Eq_refl (ceqax x x) (id x)))             -- LawF_id
                          (\_,_,_, g, f => (Eq_refl (ceqax _ _) (g . f)))  -- LawF_comp

-- Proof that FunctorComp yields a functor
-- Eq part of FunctorComp proof
FunctorCompEqOK : {c, d, e : Category} -> (fde : Functor d e) -> (fcd : Functor c d) -> 
                                (fcdFPrf : FunctorLaws c d fcd) -> (fdeFPrf : FunctorLaws d e fde) ->
                                (x, y : Obj c) -> (f, g : Hom x y) -> f === g -> 
                                IAMap (FunctorComp fde fcd) _ _ f === IAMap (FunctorComp fde fcd) _ _ g
FunctorCompEqOK fde fcd fcdFPrf fdeFPrf x y f g pfgeq = 
  let 
    pcd = LawF_eq fcdFPrf x y f g pfgeq 
    pde = LawF_eq fdeFPrf (OMap fcd x) (OMap fcd y) (IAMap fcd x y f) (IAMap fcd x y g) pcd
  in pde

-- ID part of FunctorComp proof
FunctorCompIdOK : {c, d, e : Category} -> (fde : Functor d e) -> (fcd : Functor c d) -> 
                                (pFLcd : FunctorLaws c d fcd) -> (pFLde : FunctorLaws d e fde) ->
                                (pEqAxE : CatArrEqIsEquiv e) ->
                                let fce : Functor c e = FunctorComp fde fcd in
                                (x : Obj c) -> IAMap fce x x (IId c x) === IId e (OMap fce x)
FunctorCompIdOK {c=c} {d=d} {e=e} fde fcd pFLcd pFLde pEqAxE x  = 
  let
    mx = OMap fcd x
    mmx = OMap fde mx
    idc = IId c x
    idd = IId d mx
    ide = IId e mmx
    midc : IHom d mx mx = IAMap fcd x x idc
    midd : IHom e mmx mmx = IAMap fde mx mx idd
    mmidc : IHom e mmx mmx = IAMap fde mx mx midc
    peqd = LawF_id pFLcd x                                      -- : midc === idd (in d)
    peqe = LawF_id pFLde mx                                     -- : midd === ide (in e)
    epeqd = LawF_eq pFLde mx mx midc idd peqd                   -- : mmidc === midd (in e)
    p = Eq_trans (pEqAxE mmx mmx) mmidc midd ide epeqd peqe     -- : mmidc === ide (in e) (Goal)
  in p

-- Comp part of FunctorComp proof
FunctorCompCompOK : {c, d, e : Category} -> (fde : Functor d e) -> (fcd : Functor c d) -> 
                                (pFLcd : FunctorLaws c d fcd) -> (pFLde : FunctorLaws d e fde) ->
                                (pEqAxE : CatArrEqIsEquiv e) ->
                                let fce : Functor c e = FunctorComp fde fcd in
                                (x, y, z : Obj c) -> (g : Hom y z) -> (f : Hom x y) 
                                -> (AMap fce (g . f)) === (AMap fce g) . (AMap fce f)
FunctorCompCompOK {c=c} {d=d} {e=e} fde fcd pFLcd pFLde pEqAxE x y z g f = 
  let
    -- cat c entities:
    cgf = g . f
    -- cat d entities:
    mx : Obj d = OMap fcd x
    my : Obj d = OMap fcd y
    mz : Obj d = OMap fcd z
    mg : IHom d my mz = IAMap fcd y z g
    mf : IHom d mx my = IAMap fcd x y f
    mcgf : IHom d mx mz = IAMap fcd x z cgf
    cmgmf : IHom d mx mz = mg . mf
    -- cat e entities:
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
    p = Eq_trans (pEqAxE mmx mmz) mmcgf mcmgmf cmmgmmf pr1 r2         -- mm (g.f) = mmg . mmf
  in p


FunctorCompYieldsaFunctor : {c, d, e : Category} -> (fde : Functor d e) -> (fcd : Functor c d) -> 
                                FunctorLaws c d fcd -> FunctorLaws d e fde ->
                                CategoryAx e ->
                                FunctorLaws c e (FunctorComp fde fcd)
FunctorCompYieldsaFunctor {c=c} {d=d} {e=e} fde fcd pFLcd pFLde caxe = 
  let pEqAxE = (Law_arrEqIsEquiv caxe) 
  in MkFunctorLaws 
    (FunctorCompEqOK fde fcd pFLcd pFLde) 
    (FunctorCompIdOK fde fcd pFLcd pFLde pEqAxE)
    (FunctorCompCompOK fde fcd pFLcd pFLde pEqAxE)
