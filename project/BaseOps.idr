module Plib.BaseOps

%access public export
%default total

--------------------------------------------------------------------------------
-- Predicates (based on Booleans, not Props)
--------------------------------------------------------------------------------

--------------------------------------------------------------------------------
--         IsTrue
--------------------------------------------------------------------------------

||| Satisfiable iff b = True
|||    Note: this takes zero bits to represent
|||    Note: same as Data.So
|||
||| @ b the boolean that we expect to be True
data IsTrue : (b : Bool) -> Type where
  ItsTrue : IsTrue True

Uninhabited (IsTrue False) where  
  uninhabited ItsTrue impossible

--+-------------------------------------------
--+  Example: Nat pred that isn't defined on Z
--+ ------------------------------------------

my_pred : (n : Nat) -> {auto prec : IsTrue (n /= Z)} -> Nat
my_pred Z {prec = prec} = absurd prec
my_pred (S p) {prec = ItsTrue} = p

test_my_pred : my_pred 3 = 2
test_my_pred = Refl

test_my_pred2 : (p : Nat) -> my_pred (S p) = p
test_my_pred2 _ = Refl


--------------------------------------------------------------------------------
--         TRefine: Type Refinement
--           `TRefine Nat (/= Z)` is inhabited by `(n * ItsTrue)` when n isn't Z
--------------------------------------------------------------------------------

||| Satisfied by pairs, (v ** prf), such v:A and prf : P v
|||
||| @ A the type to be refined
||| @ P the predicate refining A
TRefine : (A : Type) -> (P : A -> Type) -> Type
TRefine A P = (x : A ** P x)

TRefineB : (A : Type) -> (P : A -> Bool) -> Type
TRefineB A P = (x : A ** IsTrue (P x))


--+-------------------------------------------
--+  Example: Nat pred, again, using TRefineB
--+ ------------------------------------------

pred2 : TRefineB Nat (/= Z) -> Nat
pred2 (Z ** prf) = absurd prf
pred2 (S p ** _) = p
-- Note: Idris can't case-split inside a DPair, so had to do it manually


--------------------------------------------------------------------------------
--         TRefine2: Type Refinement
--           Similar to TRefineB above, except with a return type
--           I thought it might make it that Idris could case on the value,
--            but it didn't work
--------------------------------------------------------------------------------

TRefine2 : (A : Type) -> (A -> Bool) -> Type -> Type
TRefine2 a p b = (x : a) -> (p x = True) -> b


--+-------------------------------------------
--+  Example: Nat pred, again, using TRefine2
--+ ------------------------------------------

pred3 : TRefine2 Nat (/= Z)  Nat
-- pred3 = ?pred3_rhs
-- Idris gives above: had to manually adds args
-- But Idris gives garbage when case-splitting first arg 
--    pred3 v v = ?h_1
--    pred3 v v = ?h_2
pred3 Z prf = absurd prf
pred3 (S p) _ = p 
