
import Data.List
import Category

%default total

 
--------------------------------------------------------------------------------
-- Categories: 
--    programming lang types & functions, 
--    PL types with functions A -> List(B)
--------------------------------------------------------------------------------


---+----------------------------------------------
---+ PLType, aka "Set", Category
---+----------------------------------------------

PLTypeCat : Category
PLTypeCat = MkCategory 
  Type                    -- Obj  : Type
  (\a,b => a->b)          -- Hom  : Obj -> Obj -> Type
  (\_, x => x)            -- Id   : (x : Obj) -> Hom x x
  (\g,f => \x => g (f x)) -- Comp : {x, y, z : Obj} -> Hom y z -> Hom x y -> Hom x z


PLTypeCatAx : CategoryAx PLTypeCat
PLTypeCatAx = MkCatAx
  (=)                  -- ObjEq
  (=)                  -- ArrowEq
  (\f => Refl)         -- Law_idR   : {x, y : Obj c} -> (f : Hom c x y) -> f = (Comp c f (Id c x))
  (\f => Refl)         -- Law_idL   : {x, y : Obj c} -> (f : Hom c x y) -> f = (Comp c (Id c x) f)
  (\f,g,h => Refl)     -- Law_assoc : {x, y, z, w : Obj c} -> (f : Hom c x y) -> (g : Hom c y z) -> (h : Hom c z w) 
                       --              -> (Comp c (Comp c h g) f) = (Comp c h (Comp c g f))


---+-----------------------------------------------
---+ Category with PL-types, morphisms A => List(B)
---+-----------------------------------------------

-- First attempt had `flatmap f xs = flatten (map f xs)` but it was awkward 
-- because (a) `map` is a virtual and (b) the separation made it harder to read

flatmap : (a -> List b) -> List a -> List b
flatmap f [] = []
flatmap f (x :: xs) = (f x) ++ (flatmap f xs)

FMCat : Category
FMCat = MkCategory 
  Type                           -- Obj  : Type
  (\a,b => a -> List b)          -- Hom  : Obj -> Obj -> Type
  (\a, x => [x])                 -- Id   : (x : Obj) -> Hom x x
  (\g,f, x => flatmap g (f x))   -- Comp : {x, y, z : Obj} -> Hom y z -> Hom x y -> Hom x z
 


---+-----------------------------------------------
---+ Proof that FMCat satisfies axioms
---+-----------------------------------------------

-- flatmap on `\y => [y]` is the identity
lem_flatmap_id : (ys : List a) -> ys = flatmap (\y => [y]) ys
lem_flatmap_id [] = Refl
lem_flatmap_id (y :: ys) = let ih = lem_flatmap_id ys in cong ih

-- flatmap distributes over append
lem_fm_append: (h : c -> List d) -> (zs1, zs2 : List c) -> (flatmap h zs1) ++ (flatmap h zs2) =  flatmap h (zs1 ++ zs2)
lem_fm_append h [] _ = Refl
lem_fm_append h (z :: zs) zs2 = let 
                                  ih = lem_fm_append h zs zs2 
                                  apph = sym $ appendAssociative (h z) (flatmap h zs) (flatmap h zs2) 
                                in trans apph (cong ih) 

-- flatmap is associative (using an argument, ys)
lem_fm_assoc : (g : b -> List c) -> (h : c -> List d) -> (ys : List b) 
                 -> flatmap (\y => flatmap h (g y)) ys = flatmap h (flatmap g ys)
lem_fm_assoc g h [] = Refl
lem_fm_assoc g h (y :: ys) = let
                               ih = lem_fm_assoc g h ys
                               p1 = lem_fm_append h (g y) (flatmap g ys)
                             in trans (cong ih) p1


FunEx : (f,g : a->b) -> Type
FunEx f g = (x : _) -> (f x) = (g x)

-- flatmap is associative (using function equality via FunEx):
-- (f o (g o h)) = ((f o g) o h) <=> (\x => flatmap (g o h) (f x)) = (\x => flatmap h ((f o g) x))
lem_fm_assoc' : (f : a -> List b) -> (g : b -> List c) -> (h : c -> List d)  
                 -> FunEx (\x => flatmap (\y => flatmap h (g y)) (f x)) (\x => flatmap h (flatmap g (f x)))
lem_fm_assoc' f g h x with (f x)
  lem_fm_assoc' f g h x | [] = Refl
  lem_fm_assoc' f g h x | (y :: ys) = let
                                        ih = lem_fm_assoc' f g h x | ys
                                        p1 = lem_fm_append h (g y) (flatmap g ys)
                                      in trans (cong ih) p1


FMCatAx : CategoryAx FMCat
FMCatAx = MkCatAx
  --  ObjEq     : (Obj c) -> (Obj c) -> Type
  --  ArrowEq   : {x, y : Obj c} -> (Hom c x y) -> (Hom c x y) -> Type
  --  Law_idL   : {x, y : Obj c} -> (a : Hom c x y) -> ArrowEq a ((Id c x) . a)
  --  Law_idR   : {x, y : Obj c} -> (a : Hom c x y) -> ArrowEq a (a . (Id c y))
  --  Law_assoc : {x, y, z, w : Obj c} -> (p : Hom c x y) -> (q : Hom c y z) -> (r : Hom c z w) 
  --              -> ArrowEq ((p . q) . r) (p . (q . r))
  (=)
  FunEx
  (\f, x => sym $ appendNilRightNeutral (f x))
  (\f, x => lem_flatmap_id (f x)) 
  (\f,g,h, x => lem_fm_assoc g h (f x)) -- OR: lem_fm_assoc' 
