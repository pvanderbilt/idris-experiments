module Functors

import CatMath
import CatCore
import CatConstructions
import CatOps
import Categories
import Data.List

%access public export
%default total



---+-----------------------------------------------
---+ Definition of the List functor
---+   and a proof that it is a functor
---+-----------------------------------------------

-- map on lists (my definition for conveience)

listMap : (a -> b) -> List a -> List b
listMap f [] = []
listMap f (x :: xs) = f x :: listMap f xs

-- The List Functor

ListFunctor : EndoFunctor PLTypeCat
ListFunctor = MkFunctor List (\a,b, f => listMap f)

-- Proof that List is a functor

ListFunctorPrf : EndoFunctorLaws PLTypeCat ListFunctor
ListFunctorPrf = MkFunctorLaws FEqPrf FIdPrf FCompPrf
  where
    --  LawF_eq   : (a, b : Type) -> (f, g : a->b) -> f === g -> AMap fcd f === AMap fcd g  -- functor preserves ===
    --  LawF_id   : (x : Type) -> AMap fcd (id x) === id (OMap fcd x)                       -- functor preserves id
    --  LawF_Comp : (x, y, z : Type) -> (g : Hom y z) -> (f : Hom x y) ->                   -- functor preserves comp
    --                 AMap fcd (g . f) === (AMap fcd g) . (AMap fcd f)
    FEqPrf : (a, b : Obj PLTypeCat) -> (f, g : IHom PLTypeCat a b) -> (IArrowEq PLTypeCat a b f g)
            -> AMap ListFunctor f === AMap ListFunctor g
    FEqPrf a b f g pEq [] = Refl
    FEqPrf a b f g pEq (x::xs) = ap2 (::) (pEq x) (FEqPrf a b f g pEq xs)
    
    FIdPrf : (a : Obj PLTypeCat) -> (AMap ListFunctor (IId PLTypeCat a)) === (IId PLTypeCat (OMap ListFunctor a))
    FIdPrf a [] = Refl
    FIdPrf a (x::xs) = ap2 (::) Refl (FIdPrf a xs)
    
    FCompPrf : (a, b, c : Obj PLTypeCat) -> (g : IHom PLTypeCat b c) -> (f : IHom PLTypeCat a b) 
               -> AMap ListFunctor (g . f) === (AMap ListFunctor g) . (AMap ListFunctor f)
    FCompPrf a b c g f [] = Refl
    FCompPrf a b c g f (x::xs) = ap2 (::) Refl (FCompPrf a b c g f xs)
 

---+-----------------------------------------------
---+ Definition of the Reader functor
---+   and a proof that it is a functor (but FAILS)
---+-----------------------------------------------

ReaderFunctor : (r : Type) -> EndoFunctor PLTypeCat
ReaderFunctor r = MkFunctor (\a => r->a) (\a,b, f => (\rf, x => f (rf x)))

ReaderFunctorPrf : (r : Type) -> EndoFunctorLaws PLTypeCat (ReaderFunctor r)
ReaderFunctorPrf r = MkFunctorLaws FEqPrf FIdPrf FCompPrf
  where
    F : EndoFunctor PLTypeCat
    F = (ReaderFunctor r)
    
    -- FEqPrf : (a, b : Type) -> (f, g : a->b) -> FunEx f g -> (\rf, x => f (rf x)) (\rf, x => g (rf x))
    --   so needs ... -> (\x => f (rf x)) = (\x => g (rf x)) but they are not = (but are ===)
    FEqPrf : (a, b : Obj PLTypeCat) -> (f, g : IHom PLTypeCat a b) -> (IArrowEq PLTypeCat a b f g)
            -> AMap F f === AMap F g
    FEqPrf a b f g pEq rf = ?FEqPrf -- goal: (\x1 => f (rf x1)) = (\x1 => g (rf x1)), given f === g

    -- FIdPrf : (a : Type) -> FunEx (\rf, x => (\x:a => x) (rf x)) (\rf:r->a => rf)
    FIdPrf : (a : Obj PLTypeCat) -> (AMap F (IId PLTypeCat a)) === (IId PLTypeCat (OMap F a))
    FIdPrf a rf = Refl -- (\x1 => rf x1) = rf
     
    -- FCompPrf : (a, b, c : Type) -> (g : b->c) -> (f : a->b) -> FunEx 
    --    (\rf, x => (g . f) (rf x)) 
    --    ((\rf, x => g (rf x)) . (\rf, x => f (rf x)))
    FCompPrf : (a, b, c : Obj PLTypeCat) -> (g : IHom PLTypeCat b c) -> (f : IHom PLTypeCat a b) 
               -> IArrowEq PLTypeCat (r->a) (r->c) (AMap F (g . f)) ((AMap F g) . (AMap F f))
    FCompPrf a b c g f rf = Refl -- (\x1 => g (f (rf x1))) = (\x1 => g (f (rf x1)))
