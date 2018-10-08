module Test

import CatCore
import CatConstructions

%default total

UnitCat : Category
UnitCat = MkCategory 
  ()                 -- Obj : Type
  (\_,_ => ())       -- Hom    : Obj -> Obj -> Type
  (\_ => ())         -- Id  : (x : Obj) -> Hom x x
  (\_,_ => ())       -- Comp : (x, y, z : Obj) -> Hom y z -> Hom x y -> Hom x z
  (\p,q => p=q)      -- ArrowEq : {x, y : Obj c} -> (f, g : Hom x y) -> Type


UnitCatAx : CategoryAx UnitCat
UnitCatAx = MkCatAx Law_idR Law_idL Law_assoc
  where
    c : Category
    c = UnitCat
    Law_idR   : {x, y : Obj c} -> (f : Hom x y) -> f === f . (id x)
    Law_idR   = (\f => ?h1)
    Law_idL   : {x, y : Obj c} -> (f : Hom x y) -> f === (id y) . f
    Law_assoc : {x, y, z, w : Obj c} -> (f : Hom x y) -> (g : Hom y z) -> (h : Hom z w) 
                  ->  (.) {c=c} (h . g) f === h . (g . f)

{-
  (\() => Refl)    -- Law_idR : {x, y : Obj c} -> (a : Hom x y) -> ArrowEq a ((id x) >>> a)
  (\() => Refl)    -- Law_idL : {x, y : Obj c} -> (a : Hom x y) -> ArrowEq a (a >>> (id y))
  (\p,q,r => Refl) -- Law_assoc : (p : Hom x y) -> (q : Hom y z) -> (r : Hom z w) -> ArrowEq (p >>>(q>>>r)) ((p>>>q)>>>r)
-}

{- FINALLY some "where" based definitions that work. -}
{-
PreorderCatAx' :  (p : Preorder) -> CategoryAx (PreorderCat p)
PreorderCatAx' p = MkCatAx Law_idR' Law_idL' Law_assoc'
  where
    Law_idR' : {x, y : Elem p} -> (f : Rel p x y) -> 
              FlatEq f (Rel_Transitive p (Rel_Reflexive p x) f)
    Law_idR' f = TheyBEq _ _ 

    Law_idL' : {x, y : Elem p} -> (f : Rel p x y) -> 
              FlatEq f (Rel_Transitive p f (Rel_Reflexive p y))
    Law_idL' f = TheyBEq _ _ 

    Law_assoc' : {x, y, z, w : Elem p} -> 
                (f : Rel p x y) -> (g : Rel p y z) -> (h : Rel p z w) ->
                    FlatEq (Rel_Transitive p f (Rel_Transitive p g h)) 
                           (Rel_Transitive p (Rel_Transitive p f g) h)
    Law_assoc' f g h = TheyBEq _ _

PreorderCatAx'' :  (p : Preorder) -> CategoryAx (PreorderCat p)
PreorderCatAx'' p = MkCatAx Law_idR' Law_idL' Law_assoc'
  where
    C : Category
    C =  PreorderCat p
    Law_idR'   : {x, y : Obj C} -> (f : Hom x y) -> f === (.) {c=C} f (id {c=C} x)
    Law_idR' f = TheyBEq _ _ 
    Law_idL'   : {x, y : Obj C} -> (f : Hom x y) -> f === (.) {c=C} (id y) f
    Law_idL' f = TheyBEq _ _ 
    Law_assoc' : {x, y, z, w : Obj C} -> (f : Hom x y) -> (g : Hom y z) -> (h : Hom z w) 
                    ->  (.) {c=C} ((.) {c=C} h g) f === (.) {c=C} h ((.) {c=C} g f)
    Law_assoc' f g h = TheyBEq _ _

-}

{- Not done
---+------------------------------------------
---+ Bool with AND forms a monoid and a category
---+------------------------------------------

BoolMonoid : Monoid
BoolMonoid = MkMonoid Bool True (\x,y => x && y)

lemBoolAndTrue : (x : Bool) -> (x && True) = x
lemBoolAndTrue False = Refl
lemBoolAndTrue True = Refl

lemAndAssoc :  (x,y,z : Bool) -> ((x && y) && z) = (x && (y && z))
lemAndAssoc False y z = Refl
lemAndAssoc True False z = Refl
lemAndAssoc True True z = Refl

BoolMonoidAx : MonoidAx BoolMonoid
BoolMonoidAx = MkMonoidAx  (\x => Refl) (\x => lemBoolAndTrue x) ?h3

---+------------------------------------------
---+ Bool with AND forms a monoid and a category
---+------------------------------------------

BAnd : (x,y : Bool) -> Bool
BAnd False y = False
BAnd True y = y

BoolMonoid : Monoid
BoolMonoid = MkMonoid Bool True BAnd

lemBoolAndTrue : (x : Bool) -> x = (BAnd x True)
lemBoolAndTrue False = Refl
lemBoolAndTrue True = Refl

lemAndAssoc :  (x,y,z : Bool) -> (BAnd (BAnd z y) x) = (BAnd z (BAnd y x))
lemAndAssoc x y False = Refl
lemAndAssoc x y True = Refl

BoolMonoidAx : MonoidAx BoolMonoid
BoolMonoidAx = MkMonoidAx  (\x => Refl) lemBoolAndTrue lemAndAssoc

-}
