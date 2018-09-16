module Categories

import CatCore
import CatConstructions
import Data.List

%default total


--------------------------------------------------------------------------------
-- Categories: 
--    Empty, Unit
--    programming lang types & functions, 
--    PL types with functions A -> List(B)
--------------------------------------------------------------------------------

---+----------------------------------------------
---+ Empty and Unit Categories
---+----------------------------------------------

EmptyCat : Category
EmptyCat = MkCategory 
  Void                -- Obj : Type
  (\x,y => Void)      -- Hom    : Obj -> Obj -> Type
  (\p => absurd p)    -- Id  : (x : Obj) -> Hom x x
  (\p,q => absurd p)  -- Comp : (x, y, z : Obj) -> Hom y z -> Hom x y -> Hom x z
  (\p,q => p=q)
  
EmptyCatAx : CategoryAx EmptyCat
EmptyCatAx = MkCatAx 
  (\p => absurd p)     -- Law_idR : {x, y : Obj c} -> (a : Hom x y) -> ArrowEq a ((id x) >>> a)
  (\q => absurd q)     -- Law_idL : {x, y : Obj c} -> (a : Hom x y) -> ArrowEq a (a >>> (id y))
  (\p,q,r => absurd p) -- Law_assoc : (p : Hom x y) -> (q : Hom y z) -> (r : Hom z w) 
                       --    -> ArrowEq (p >>>(q>>>r)) ((p>>>q)>>>r)

UnitCat : Category
UnitCat = MkCategory 
  ()                 -- Obj : Type
  (\_,_ => ())       -- Hom    : Obj -> Obj -> Type
  (\_ => ())         -- Id  : (x : Obj) -> Hom x x
  (\_,_ => ())       -- Comp : (x, y, z : Obj) -> Hom y z -> Hom x y -> Hom x z
  (\p,q => p=q)      -- ArrowEq : {x, y : Obj c} -> (f, g : Hom x y) -> Type


UnitCatAx : CategoryAx UnitCat
UnitCatAx = MkCatAx 
  (\() => Refl)    -- Law_idR : {x, y : Obj c} -> (a : Hom x y) -> ArrowEq a ((id x) >>> a)
  (\() => Refl)    -- Law_idL : {x, y : Obj c} -> (a : Hom x y) -> ArrowEq a (a >>> (id y))
  (\p,q,r => Refl) -- Law_assoc : (p : Hom x y) -> (q : Hom y z) -> (r : Hom z w) -> ArrowEq (p >>>(q>>>r)) ((p>>>q)>>>r)
  

--------------------------------------------------------------------------------
-- Monoids & Monoid-related categories
--
-- Monoid and MonoidCat (with laws)
-- Any single element Category is a Monoid
-- Monoids under Homorphisms form a category
--------------------------------------------------------------------------------

---+------------------------------------------
---+ Monoids & axioms
---+------------------------------------------

record Monoid where
  constructor MkMonoid
  S  : Type
  E  : S
  Op : S -> S -> S
  
record MonoidAx (m : Monoid) where 
  constructor MkMonoidAx
  law_EL : (a : (S m)) -> a = (Op m (E m) a)
  law_ER : (a : (S m)) -> a = (Op m a (E m))
  law_assoc : (c,b,a : (S m)) -> (Op m (Op m a b) c) = (Op m a (Op m b c)) 

---+------------------------------------------
---+ Every monoid is a category
---+------------------------------------------

MonoidCat : (m : Monoid) -> Category
MonoidCat m = MkCategory 
  ()                   -- Obj : Type
  (\_,_ => (S m))      -- Hom    : Obj -> Obj -> Type
  (\_ => (E m))        -- Id  : (x : Obj) -> Hom x x
  (\p,q => (Op m p q)) -- Comp : (x, y, z : Obj) -> Hom y z -> Hom x y -> Hom x z
  (\a,b => a=b)        -- ArrowEq : {x, y : Obj c} -> (Hom x y) -> (Hom x y) -> Ty

MonoidCatAx : (m : Monoid) ->  (max : MonoidAx m) -> CategoryAx (MonoidCat m)
MonoidCatAx m max = MkCatAx 
  (law_ER max)         -- Law_idR : {x, y : Obj c} -> (a : Hom x y) -> ArrowEq c a ((id x) >>> a)
  (law_EL max)         -- Law_idL : {x, y : Obj c} -> (a : Hom x y) -> ArrowEq c a (a >>> (id y))
  (law_assoc max)      -- Law_assoc : (a,b,c : _) -> ArrowEq (a>>>(b>>>c)) ((a>>>b)>>>c)

---+------------------------------------------
---+ Any 1 object category is a monoid
---+------------------------------------------

OneObjCat2Monoid : (c : Category) -> ((Obj c) = ()) -> Monoid
OneObjCat2Monoid c p = let theObj : Obj c = rewrite p in () 
                       in MkMonoid (Hom theObj theObj)  (id theObj) (IComp c)

OneObjCat2Monoid2 : (c : Category) -> (x : Obj c ** (y : Obj c) -> x=y) -> Monoid
OneObjCat2Monoid2 c (x ** _) = MkMonoid (Hom x x)  (id x) (IComp c)



---+----------------------------------------------
---+ In fact, for *any* category and *any* object x, 
---+   the arrows of Hom x x form a monoid
---+----------------------------------------------

{- A previous attempt failed because of abstract ArrowId,
   which is why this uses CategoryAxEq instead of CategoryAx -}

Hom2Monoid : (c : Category) -> (cax: CategoryAxEq c) -> (x : Obj c) 
             -> (m : Monoid ** ((S m) = (Hom x x) , MonoidAx m))
Hom2Monoid c cax x = 
  let
    m = MkMonoid (Hom x x)  (id x) (IComp c)
    ler = Law_idR cax 
    lel = Law_idL cax 
    lassoc = Law_assoc cax
    max : MonoidAx m = MkMonoidAx lel ler lassoc
  in (m ** (Refl , max))



---+--------------------------------------------------------
---+ Monoid Homorphisms and related
---+
---+ `MonoidHom m1 m2` is a type of (f ** (pe, pop)) triples
---+   where `f` is a mapping from m1's set to m2's,
---+   pe is a proof that f preserves identity and
---+   pop is a proof that f preserves Op 
---+ `MonoidIdHom m` is the identity homomorphism for m
---+ `MonoidIdComp` is monoid homomorphism composition
---+---------------------------------------------------------

MonoidHom : (m1, m2 : Monoid) -> Type
MonoidHom m1 m2 = (f : (S m1 -> S m2) ** 
                   ( (f (E m1) = E m2) , 
                     (x, y : S m1) -> (f (Op m1 x y) = Op m2 (f x) (f y)) ) )

MonoidIdHom : (m : Monoid) -> MonoidHom m m
MonoidIdHom m = (id ** (Refl , (\_,_ => Refl)))

MonoidHomComp : {m1, m2, m3 : Monoid} -> MonoidHom m2 m3 -> MonoidHom m1 m2 -> MonoidHom m1 m3
MonoidHomComp h23 h12 = 
  let 
    (f12 ** (pid12 , pcomp12)) = h12 
    (f23 ** (pid23 , pcomp23)) = h23 
  in 
    ((f23 . f12) ** 
     (trans (cong {f=f23} pid12) pid23 , 
     (\x, y => let 
                 -- p23R : f23 (f12 (Op m1 x y)) = f23 (Op m2 (f12 x) (f12 y))
                 -- p23L : f23 (Op m2 (f12 x) (f12 y)) = Op m3 (f23 (f12 x)) (f23 (f12 y))
                 p23R = (cong {f=f23} (pcomp12 x y))
                 p23L = pcomp23 (f12 x) (f12 y)
               in trans p23R p23L) ))


---+--------------------------------------------------------
---+ The set of monoids form a category under homomorphism
---+--------------------------------------------------------

MonoidsCat : Category
MonoidsCat = MkCategory Monoid MonoidHom MonoidIdHom MonoidHomComp (=)



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
  FunEx                     -- ArrowEq : {x, y : Obj} -> (f, g : Hom x y) -> Type
  

PLTypeCatAx : CategoryAx PLTypeCat
PLTypeCatAx = MkCatAx
  (\f, x => Refl)         -- Law_idR   : {x, y : Obj c} -> (f : Hom x y) -> f = ((.) f (id x))
  (\f, x => Refl)         -- Law_idL   : {x, y : Obj c} -> (f : Hom x y) -> f = ((.) (id x) f)
  (\f,g,h, x => Refl)     -- Law_assoc : {x, y, z, w : Obj c} -> (f : Hom x y) -> (g : Hom y z) -> (h : Hom z w) 
                       --              -> ((.) ((.) h g) f) = ((.) h ((.) g f))

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
  FunEx                          -- ArrowEq : {x, y : Obj} -> (f, g : Hom x y) -> Type


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
  --  Law_idL   : {x, y : Obj c} -> (a : Hom x y) -> ArrowEq a ((id x) . a)
  --  Law_idR   : {x, y : Obj c} -> (a : Hom x y) -> ArrowEq a (a . (id y))
  --  Law_assoc : {x, y, z, w : Obj c} -> (p : Hom x y) -> (q : Hom y z) -> (r : Hom z w) 
  --              -> ArrowEq ((p . q) . r) (p . (q . r))
  (\f, x => sym $ appendNilRightNeutral (f x))
  (\f, x => lem_flatmap_id (f x)) 
  (\f,g,h, x => lem_fm_assoc g h (f x)) -- OR: lem_fm_assoc' 

---+-----------------------------------------------
---+ Initial and Terminal Objects for PLTypes
---+-----------------------------------------------

lemVoidFuncsEq: {a : Type} -> (f, g : Void -> a) ->  FunEx f g
lemVoidFuncsEq f g x impossible

pl_ioPrf : IsInitial {c = PLTypeCat} Void
pl_ioPrf = (\a => absurd, lemVoidFuncsEq)

lemUnitFuncsEq: {a : Type} -> (f, g : a -> Unit) -> FunEx f g
lemUnitFuncsEq f g x with (f x)
  lemUnitFuncsEq f g x | () with (g x)
    lemUnitFuncsEq f g x | () | () = Refl

pl_toPrf : IsTerminal {c = PLTypeCat} ()
pl_toPrf = (\a, x => (), lemUnitFuncsEq)
