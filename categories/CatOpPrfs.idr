module CatOpPrfs

import CatMath
import CatCore
import CatConstructions
import CatOps

%access public export
%default total

-- Predicate saying that a category's arrow equality (===) is an equivalence relation
CatArrEqIsEquiv : (c : Category) -> Type
CatArrEqIsEquiv c = (x, y : Obj c) -> IsEquivRel (IHom c x y) (IArrowEq c x y)

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



---+---------------------------------------------------
---+  ProdCatPrf: Proof that ProdCat is a category
---+---------------------------------------------------

PCPIdR : (c1, c2 : Category) -> CategoryAx c1 -> CategoryAx c2 -> 
         let PC = ProdCat c1 c2 in (x,y : Obj PC) -> (f : IHom PC x y) -> f === f . (id x)
PCPIdR c1 c2 plc1 plc2 = (\(x1, x2), (y1, y2), (f1, f2) => (Law_idR plc1 f1 , Law_idR plc2 f2))

PCPIdL : (c1, c2 : Category) -> CategoryAx c1 -> CategoryAx c2 -> 
         let PC = ProdCat c1 c2 in (x,y : Obj PC) -> (f : IHom PC x y) -> f === (id y) . f
PCPIdL c1 c2 plc1 plc2 = (\(x1, x2), (y1, y2), (f1, f2) => (Law_idL plc1 f1 , Law_idL plc2 f2))

PCPAssoc : (c1, c2 : Category) -> CategoryAx c1 -> CategoryAx c2 -> let PC = ProdCat c1 c2 in 
           (x, y, z, w : Obj PC) -> (f : IHom PC x y) -> (g : IHom PC y z) -> (h : IHom PC z w) 
                -> (IArrowEq PC x w ((h . g) . f) (h . (g . f)))
PCPAssoc c1 c2 plc1 plc2 = (\(x1, x2), (y1, y2), (z1, z2), (w1, w2), (f1, f2), (g1, g2), (h1, h2)  
                           => (Law_assoc plc1 f1 g1 h1 , Law_assoc plc2 f2 g2 h2))

PCArrEqIsEquiv : (c1, c2 : Category) -> CategoryAx c1 -> CategoryAx c2 -> let PC = ProdCat c1 c2 in 
                 (x, y : Obj PC) -> IsEquivRel (IHom PC x y) (IArrowEq PC x y)
PCArrEqIsEquiv c1 c2  plc1 plc2 = (\(x1, x2), (y1, y2) => 
               let
                 p1 = Law_arrEqIsEquiv plc1 x1 y1
                 p2 = Law_arrEqIsEquiv plc2 x2 y2
               in MkIsEquivRel 
                 -- Eq_refl  : (f : a) -> f ==== f
                 (\(f1, f2) => (Eq_refl p1 f1, Eq_refl p2 f2)) 
                 
                 -- Eq_sym   : (f, g : a) -> f === g -> g === f  
                 (\(f1, f2), (g1, g2), (efg1, efg2) 
                   => (Eq_sym p1 f1 g1 efg1, Eq_sym p2 f2 g2 efg2))  
                
                -- Eq_trans : (f, g, h : a) -> f === g -> g === h -> f === g
                (\(f1, f2), (g1, g2), (h1, h2), (efg1, efg2), (egh1, egh2)
                   => (Eq_trans p1 f1 g1 h1 efg1 egh1, Eq_trans p2 f2 g2 h2 efg2 egh2)) 
               )

ProdCatPrf: (c1, c2 : Category) -> CategoryAx c1 ->  CategoryAx c2 -> CategoryAx (ProdCat c1 c2)
ProdCatPrf c1 c2 plc1 plc2 = 
  MkCatAx (PCPIdR c1 c2 plc1 plc2 _ _) 
          (PCPIdL c1 c2 plc1 plc2 _ _) 
          (PCPAssoc c1 c2 plc1 plc2 _ _ _ _) 
          (PCArrEqIsEquiv c1 c2  plc1 plc2)

