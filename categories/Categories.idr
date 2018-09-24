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
  Void                 -- Obj : Type
  (\x,y => Void)       -- Hom : (x, y : Obj) -> Type
  (\x => absurd x)     -- Id : (x : Obj) -> Hom x x
  (\g,f => absurd g)   -- Comp : (g : Hom y z) -> (f : Hom x y) -> Hom x z
  (\f,g => f=g)        -- ArrowEq : (f, g : Hom x y) -> Type
  
EmptyCatAx : CategoryAx EmptyCat
EmptyCatAx = MkCatAx 
  (\f => absurd f)     -- Law_idR : (f : Hom x y) -> f === f . (id x)
  (\f => absurd f)     -- Law_idL : (f : Hom x y) -> f === (id y) . f
  (\f,g,h => absurd f) -- Law_assoc : (f, g, h : _) -> (h . g) . f === h . (g . f)

UnitCat : Category
UnitCat = MkCategory 
  ()                 -- Obj : Type
  (\_,_ => ())       -- Hom : (x, y : Obj) -> Type
  (\_ => ())         -- Id : (x : Obj) -> Hom x x
  (\_,_ => ())       -- Comp : (g : Hom y z) -> (f : Hom x y) -> Hom x z
  (\f,g => f=g)      -- ArrowEq : (f, g : Hom x y) -> Type


UnitCatAx : CategoryAx UnitCat
UnitCatAx = MkCatAx 
  (\() => Refl)      -- Law_idR : (f : Hom x y) -> f === f . (id x)
  (\() => Refl)      -- Law_idL : (f : Hom x y) -> f === (id y) . f
  (\f,g,h => Refl)   -- Law_assoc : (f, g, h : _) -> (h . g) . f === h . (g . f)
  

---+------------------------------------------
---+ Orders
---+------------------------------------------

data IsTrue : Bool -> Type where
  ItsTrue : (b : Bool) -> IsTrue b

record DecideablePreorder where
  constructor MkDecPreorder
  Elem : Type
  LTE : Elem -> Elem -> Bool
  LTE_Reflexive : (x : Elem) -> IsTrue (LTE x x)
  LTE_Transitive : {x, y, z : Elem} -> IsTrue (LTE x y) -> IsTrue (LTE y z) 
                   -> IsTrue (LTE x z)
  
DecPreorderCat : (p : DecideablePreorder) -> Category
DecPreorderCat p = MkCategory
  (Elem p)                         -- Obj : Type
  (\x, y => IsTrue (LTE p x y))    -- Hom : (x, y : Obj) -> Type
  (\x => LTE_Reflexive p x)        -- Id : (x : Obj) -> Hom x x
  (\g,f => LTE_Transitive p f g)   -- Comp : (g : Hom y z) -> (f : Hom x y) -> Hom x z
  (=)                              -- ArrowEq : (f, g : Hom x y) -> Type


Relation : (a : Type) -> Type 
Relation a = a -> a -> Type 

RelReflexive : {a : Type} -> (r : Relation a) ->Type
RelReflexive {a} r = (x : a) -> r x x

RelTransitive : {a : Type} -> (r : Relation a) -> Type 
RelTransitive {a} r = {x, y, z : a} -> r x y -> r y z -> r x z 
  
record Preorder where
  constructor MkPreorder
  Elem : Type
  Rel : Relation Elem
  Rel_Reflexive : RelReflexive Rel
  Rel_Transitive : RelTransitive Rel

PreorderCat : (p : Preorder) -> Category
PreorderCat p = MkCategory
  (Elem p)                         -- Obj : Type
  (Rel p)                          -- Hom : (x, y : Obj) -> Type
  (Rel_Reflexive p)                -- Id : (x : Obj) -> Hom x x
  (\g, f => Rel_Transitive p f g)  -- Comp : (g : Hom y z) -> (f : Hom x y) -> Hom x z
  (\f, g => FlatEq f g)            -- ArrowEq : (f, g : Hom x y) -> Type

PreorderCatAx :  (p : Preorder) -> CategoryAx (PreorderCat p)
PreorderCatAx p = MkCatAx 
  (\f => TheyBEq _ _)              -- Law_idR : (f : Hom x y) -> f === f . (id x)
  (\f => TheyBEq _ _)              -- Law_idL : (f : Hom x y) -> f === (id y) . f
  (\f,g,h => TheyBEq _ _)          -- Law_assoc : (f, g, h : _) -> (h . g) . f === h . (g . f)


-- Preorder-based categories are thin, in that each HOM has at most one arrow
PreorderCatsRThin : (p : Preorder) -> IsThinCat (PreorderCat p)
PreorderCatsRThin p x y f g = TheyBEq f g




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
  (\_,_ => (S m))      -- Hom : (x, y : Obj) -> Type
  (\_ => (E m))        -- Id : (x : Obj) -> Hom x x
  (\g,f => (Op m g f)) -- Comp : (g : Hom y z) -> (f : Hom x y) -> Hom x z
  (\f,g => f=g)        -- ArrowEq : (f, g : Hom x y) -> Type

MonoidCatAx : (m : Monoid) ->  (max : MonoidAx m) -> CategoryAx (MonoidCat m)
MonoidCatAx m max = MkCatAx 
  (law_ER max)         -- Law_idR : (f : Hom x y) -> f === f . (id x)
  (law_EL max)         -- Law_idL : (f : Hom x y) -> f === (id y) . f
  (law_assoc max)      -- Law_assoc : (f, g, h : _) -> (h . g) . f === h . (g . f)

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

{- Not done -}
-- MonoidsCatAx : CategoryAx MonoidsCat
-- MonoidsCatAx = MkCatAx (\f1 => ?Law_idR) ?Law_idL ?Law_assoc

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
  Type                    -- Obj : Type
  (\a,b => a->b)          -- Hom : (x, y : Obj) -> Type
  (\a => \x => x)         -- Id : (x : Obj) -> Hom x x
  (\g,f, x => g (f x))    -- Comp : (g : Hom y z) -> (f : Hom x y) -> Hom x z
  FunEx                   -- ArrowEq : (f, g : Hom x y) -> Type
  

PLTypeCatAx : CategoryAx PLTypeCat
PLTypeCatAx = MkCatAx
  (\f, x => Refl)         -- Law_idR   : (f : Hom x y) -> f === f . (id x)
  (\f, x => Refl)         -- Law_idL   : (f : Hom x y) -> f === (id y) . f
  (\f,g,h, x => Refl)     -- Law_assoc : (f, g, h : _) -> (h . g) . f === h . (g . f)

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
  Type                           -- Obj : Type
  (\a,b => a -> List b)          -- Hom : (x, y : Obj) -> Type
  (\a, x => [x])                 -- Id : (x : Obj) -> Hom x x
  (\g,f, x => flatmap g (f x))   -- Comp : (g : Hom y z) -> (f : Hom x y) -> Hom x z
  FunEx                          -- ArrowEq : (f, g : Hom x y) -> Type


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


FMCatAx : CategoryAx FMCat
FMCatAx = MkCatAx
  (\f, x => sym $ appendNilRightNeutral (f x))  --  Law_idL   : (f : Hom x y) -> f === f . (id x)
  (\f, x => lem_flatmap_id (f x))               --  Law_idR   : (f : Hom x y) -> f === (id y) . f
  (\f,g,h, x => lem_fm_assoc g h (f x))         --  Law_assoc : (f, g, h : _) -> (h . g) . f === h . (g . f)


-- Alternate definition allowing `lem_fm_assoc'` to be the value of the last line
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



---+-----------------------------------------------
---+ Terminal and Initial Objects for PLTypes
---+-----------------------------------------------

lemUnitFuncsEq: {a : Type} -> (f, g : a -> Unit) -> FunEx f g
lemUnitFuncsEq f g x with (f x)
  lemUnitFuncsEq f g x | () with (g x)
    lemUnitFuncsEq f g x | () | () = Refl

pl_toPrf : IsTerminal {c = PLTypeCat} ()
pl_toPrf = (\a, x => (), lemUnitFuncsEq)

lemVoidFuncsEq: {a : Type} -> (f, g : Void -> a) ->  FunEx f g
lemVoidFuncsEq f g x impossible

pl_ioPrf : IsInitial {c = PLTypeCat} Void
pl_ioPrf = (\a => absurd, lemVoidFuncsEq)
