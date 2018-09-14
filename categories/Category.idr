module Category

%access public export
%default total


--------------------------------------------------------------------------------
-- Categories
--------------------------------------------------------------------------------

---+--------------------------------------
---+  The basic Category record type
---+--------------------------------------

record Category where
  constructor MkCategory
  Obj     : Type
  Hom     : (x, y : Obj) -> Type
  Id      : (x : Obj) -> Hom x x
  Comp    : {x, y, z : Obj} -> (g : Hom y z) -> (f : Hom x y) -> Hom x z
  ArrowEq : {x, y : Obj} -> (f, g : Hom x y) -> Type
  
-- Comp g f is "g after f"

-- g . f is Comp g f (is "g after f")
-- f >>> g  is "f then g"

infixr 1 >>>
(>>>) : {c : Category} -> {x, y, z : Obj c} -> Hom c x y -> Hom c y z -> Hom c x z
(>>>) {c} {x} {y} {z} f g = Comp c g f

(.) : {c : Category} -> {x, y, z : Obj c} -> Hom c y z -> Hom c x y -> Hom c x z
(.) {c} {x} {y} {z} g f = Comp c g f

---+--------------------------------------
---+  Category axioms
---+--------------------------------------

record CategoryAx (c : Category) where
  constructor MkCatAx
  Law_idR   : {x, y : Obj c} -> (f : Hom c x y) -> ArrowEq c f (Comp c f (Id c x))
  Law_idL   : {x, y : Obj c} -> (f : Hom c x y) -> ArrowEq c f (Comp c (Id c y) f)
  Law_assoc : {x, y, z, w : Obj c} -> (f : Hom c x y) -> (g : Hom c y z) -> (h : Hom c z w) 
              -> ArrowEq c (Comp c (Comp c h g) f) (Comp c h (Comp c g f))

--------------------------------------------------------------------------------
-- Some useful functions
--------------------------------------------------------------------------------

---+-----------------------------------------------
---+ FunEx: Function extensionality
---+-----------------------------------------------

FunEx : (f,g : a->b) -> Type
FunEx f g = (x : _) -> (f x) = (g x)

--------------------------------------------------------------------------------
-- Categories: (), Empty
--------------------------------------------------------------------------------

UnitCat : Category
UnitCat = MkCategory 
  ()                 -- Obj : Type
  (\_,_ => ())       -- Hom    : Obj -> Obj -> Type
  (\_ => ())         -- Id  : (x : Obj) -> Hom x x
  (\_,_ => ())       -- Comp : (x, y, z : Obj) -> Hom y z -> Hom x y -> Hom x z
  (\p,q => p=q)      -- ArrowEq : {x, y : Obj c} -> (f, g : Hom c x y) -> Type


UnitCatAx : CategoryAx UnitCat
UnitCatAx = MkCatAx 
  (\() => Refl)    -- Law_idR : {x, y : Obj c} -> (a : Hom c x y) -> ArrowEq a ((Id c x) >>> a)
  (\() => Refl)    -- Law_idL : {x, y : Obj c} -> (a : Hom c x y) -> ArrowEq a (a >>> (Id c y))
  (\p,q,r => Refl) -- Law_assoc : (p : Hom c x y) -> (q : Hom c y z) -> (r : Hom c z w) -> ArrowEq (p >>>(q>>>r)) ((p>>>q)>>>r)
  
EmptyCat : Category
EmptyCat = MkCategory 
  Void                -- Obj : Type
  (\x,y => Void)      -- Hom    : Obj -> Obj -> Type
  (\p => absurd p)    -- Id  : (x : Obj) -> Hom x x
  (\p,q => absurd p)  -- Comp : (x, y, z : Obj) -> Hom y z -> Hom x y -> Hom x z
  (\p,q => p=q)
  
EmptyCatAx : CategoryAx EmptyCat
EmptyCatAx = MkCatAx 
  (\p => absurd p)     -- Law_idR : {x, y : Obj c} -> (a : Hom c x y) -> ArrowEq a ((Id c x) >>> a)
  (\q => absurd q)     -- Law_idL : {x, y : Obj c} -> (a : Hom c x y) -> ArrowEq a (a >>> (Id c y))
  (\p,q,r => absurd p) -- Law_assoc : (p : Hom c x y) -> (q : Hom c y z) -> (r : Hom c z w) 
                       --    -> ArrowEq (p >>>(q>>>r)) ((p>>>q)>>>r)


--------------------------------------------------------------------------------
-- Older versions, in a more convenient form (but wouldn't type)
--------------------------------------------------------------------------------
{-  This had given errors:
     Can't infer argument x1 to Category.UnitCat', comp, 
     Can't infer argument x2 to Category.UnitCat', comp, 
     Can't infer argument x3 to Category.UnitCat', comp, 
     Can't infer argument x to Category.UnitCat', arreq, 
     Can't infer argument y to Category.UnitCat', arreq

-}
UnitCat' : Category
UnitCat' = MkCategory obj hom id comp arreq
  where
    obj : Type
    obj = ()
    hom : obj -> obj -> Type
    hom _ _ = ()
    id : (x : obj) -> hom x x
    id _ = ()
    comp : () -> () -> ()
    comp _ _ = ()
    --comp : (x1, x2, x3 : obj) -> hom x1 x2 -> hom x2 x3 -> hom x1 x3
    --comp _ _ _ g f = ()
    arreq : (f, g : ()) -> Type
    arreq f g = (f = g)

{- ERROR:
     Can't infer argument x to Category.UnitCatAx', law_idR, 
     Can't infer argument y to Category.UnitCatAx', law_idR, 
     Can't infer argument x1 to Category.UnitCatAx', law_idR, 
     ... and 23 more ...

UnitCatAx' : CategoryAx UnitCat
UnitCatAx' = MkCatAx law_idR law_idL law_assoc
  where
    law_idR : (f : Hom UnitCat x y) -> ArrowEq UnitCat f (Comp UnitCat f (Id UnitCat x))
    law_idR () = Refl
    --law_idR : () -> () = ()
    --law_idR () = Refl
    law_idL : (f : Hom UnitCat _ _) -> ArrowEq UnitCat f (Comp UnitCat (Id UnitCat _) f)
    law_idL () = Refl
    law_assoc : (f : ()) -> (g : ()) -> (h : ()) 
              -> (Comp UnitCat (Comp UnitCat h g) f) = (Comp UnitCat h (Comp UnitCat g f))
    law_assoc f g h = Refl
-}

 
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
  (\a,b => a=b)        -- ArrowEq : {x, y : Obj c} -> (Hom c x y) -> (Hom c x y) -> Ty

MonoidCatAx : (m : Monoid) ->  (max : MonoidAx m) -> CategoryAx (MonoidCat m)
MonoidCatAx m max = MkCatAx 
  (law_ER max)         -- Law_idR : {x, y : Obj c} -> (a : Hom c x y) -> ArrowEq c a ((Id c x) >>> a)
  (law_EL max)         -- Law_idL : {x, y : Obj c} -> (a : Hom c x y) -> ArrowEq c a (a >>> (Id c y))
  (law_assoc max)      -- Law_assoc : (a,b,c : _) -> ArrowEq (a>>>(b>>>c)) ((a>>>b)>>>c)

---+------------------------------------------
---+ Any 1 object category is a monoid
---+------------------------------------------

OneObjCat2Monoid : (c : Category) -> ((Obj c) = ()) -> Monoid
OneObjCat2Monoid c p = let theObj : Obj c = rewrite p in () 
                       in MkMonoid (Hom c theObj theObj)  (Id c theObj) (Comp c)

OneObjCat2Monoid2 : (c : Category) -> (x : Obj c ** (y : Obj c) -> x=y) -> Monoid
OneObjCat2Monoid2 c (x ** _) = MkMonoid (Hom c x x)  (Id c x) (Comp c)


---+----------------------------------------------
---+  Category Axioms with built-in = 
---+----------------------------------------------

record CategoryAxEq (c : Category) where
  constructor MkCatAxEq
  Law_idR   : {x, y : Obj c} -> (f : Hom c x y) -> f = (Comp c f (Id c x))
  Law_idL   : {x, y : Obj c} -> (f : Hom c x y) -> f = (Comp c (Id c y) f)
  Law_assoc : {x, y, z, w : Obj c} -> (f : Hom c x y) -> (g : Hom c y z) -> (h : Hom c z w) 
              -> (Comp c (Comp c h g) f) = (Comp c h (Comp c g f))


---+----------------------------------------------
---+ In fact, for *any* category and *any* object x, 
---+   the arrows of Hom x x form a monoid
---+----------------------------------------------

{- A previous attempt failed because of abstract ArrowId,
   which is why this uses CategoryAxEq instead of CategoryAx -}

Hom2Monoid : (c : Category) -> (cax: CategoryAxEq c) -> (x : Obj c) 
             -> (m : Monoid ** ((S m) = (Hom c x x) , MonoidAx m))
Hom2Monoid c cax x = 
  let
    m = MkMonoid (Hom c x x)  (Id c x) (Comp c)
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

{-
--------------------------------------------------------------------------------
-- A Category based on arrows and its mapping
--------------------------------------------------------------------------------

---+--------------------------------------
---+  ArrowCategory
---+--------------------------------------

record ArrowCategory where
  constructor MkArrowCategory
  Obj      : Type
  Arrow    : Type
  Dom      : Arrow -> Obj
  Cod      : Arrow -> Obj
  Id       : (x : Obj) -> Arrow
  IdProp   : (x : Obj) -> (Dom (Id x) = x , Cod (Id x) = x)
  Comp     : (f, g : Arrow) -> {auto peq : Cod g = Dom f} -> Arrow
  CompProp : (f, g, fog : Arrow) -> (peq : Cod g = Dom f) -> (fog = Comp f g {peq=peq}) -> (Dom fog = Dom g , Cod fog = Cod f)


---+------------------------------------------------------
---+  Mapping the arrow category to a regular one
---+    where an element of Hom x y is an arrow paired with 
---+    proofs that its dom is x and cod is y.
---+------------------------------------------------------

Arrow2Reg : ArrowCategory -> Category
Arrow2Reg ac = MkCategory 
  (Obj ac) 
  (\x,y => (a : Arrow ac ** (Dom ac a = x , Cod ac a = y)))
  (\x => (Id ac x ** IdProp ac x))
  (\hf, hg => let 
                (f ** (pfd , pfc)) = hf
                (g ** (pgd , pgc)) = hg
                peq = trans pgc (sym pfd)
                fog = Comp ac f g {peq=peq}
                (pcd , pcc) = CompProp ac f g fog peq Refl
                (pfogd , pfogc) = (trans pcd pgd , trans pcc pfc)
              in (fog ** (pfogd , pfogc)) )

{- alternate ending (GOOD)                              
                fogProp = CompProp ac f g fog peq Refl
              in rewrite (sym pgd) 
              in rewrite (sym pfc) 
              in (fog ** fogProp) )
-}

---+------------------------------------------------------------
---+  Mapping the regular category to an arrow one
---+    where arrows are triples of the form (x, y, a : Hom x y)
---+------------------------------------------------------------

{- -- NOT FINISHED
Reg2Arrow : Category -> ArrowCategory
Reg2Arrow c = MkArrowCategory
  -- Obj      : Type
  (Obj c)
  -- Arrow    : Type
  (x : Obj c ** y : Obj c ** Hom c x y)
  -- Dom      : Arrow -> Obj
  (\a => let (x ** y ** h) = a in x)
  -- Cod      : Arrow -> Obj
  ?c -- (\(_ ** y ** _) => y)
  -- Id       : (x : Obj) -> Arrow
  ?id -- (\x => (x ** x ** Id c x))
  -- IdProp   : (x : Obj) -> (Dom (Id x) = x , Cod (Id x) = x)
  ?idp -- (\x => (Refl, Refl))
  -- Comp     : (f, g : Arrow) -> {auto peq : Cod g = Dom f} -> Arrow
  ?hc -- (\f, g, peq => let ((fd, fc) ** fa) = f in let ((gd, gc) ** ga) = g in ((gd, fc) ** Comp c fa ga))
  -- CompProp : (f, g, fog : Arrow) -> (peq : Cod g = Dom f) -> (fog = Comp f g {peq=peq}) -> (Dom fog = Dom g , Cod fog = Cod f)
  ?hcp

-}
-}

