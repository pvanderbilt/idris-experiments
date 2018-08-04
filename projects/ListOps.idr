module PLib.ListOps

import BaseOps

%access public export
%default total

--------------------------------------------------------------------------------
-- List operations based on boolean preconditions
--------------------------------------------------------------------------------

--------------------------------------------------------------------------------
-- InBounds and NonEmpty based on booleans, not propositions
--------------------------------------------------------------------------------

||| Satisfiable iff `k` is a valid index into `l`
|||    Implemented by k < (length l)
|||
||| @ k the potential index
||| @ l the list into which k may be an index
MyInBounds : (l : List a) -> (k : Nat) -> Type 
MyInBounds l k = IsTrue $ lt k (length l)

||| Satisfiable iff `l` is non-empty.
|||    Implemented by (length l) > 0
|||
||| @ l the list 
MyNonEmpty : (l : List a) -> Type
MyNonEmpty l = IsTrue $ gt (length l) 0


--------------------------------------------------------------------------------
-- Indexing into lists
--------------------------------------------------------------------------------

||| Find a particular element of a list given its index.
|||
||| @ i the index
||| @ l the list 
||| @ prec a proof that the index is within bounds
my_index : (i : Nat) -> (l : List a) -> {auto prec : MyInBounds l i} -> a
my_index _ [] {prec}     = absurd prec
my_index Z (x :: _)      = x
my_index (S k) (_ :: xs) = my_index k xs 

||| Get the first element of a non-empty list
||| @ l the list 
||| @ prec proof that the list is non-empty
my_head : (l : List a) -> {auto prec : MyNonEmpty l} -> a
my_head [] {prec} = absurd prec
my_head (x :: _)  = x

||| Get the tail of a non-empty list.
||| @ l the list 
||| @ prec proof that the list is non-empty
my_tail : (l : List a) -> {auto prec : MyNonEmpty l} -> List a
my_tail [] {prec = ItsTrue} impossible
my_tail (_ :: xs)           = xs


||| Retrieve the last element of a non-empty list.
||| @ l the list 
||| @ prec proof that the list is non-empty
my_last : (l : List a) -> {auto prec : MyNonEmpty l} -> a
my_last [] {prec}      = absurd prec
my_last [x]            = x
my_last (_ :: y :: ys) = my_last (y::ys)

--------------------------------------------------------------------------------
-- Sublists
--------------------------------------------------------------------------------

||| Take the first `n` elements of `l`
|||
||| @ n how many elements to take
||| @ l the list to take them from
||| @ prec a proof that there are at least `n` elements in `l`
my_take : (n : Nat) -> (l : List a) -> {auto prec : IsTrue $ lte n (length l)} -> List a
my_take Z _             = []
my_take (S _) [] {prec} = absurd prec
my_take (S p) (x :: xs) = x :: my_take p xs

||| Proof that my_take returns `n` elements
|||
lem_myTake_returns_length_n : (n : Nat) -> (l : List a) -> {auto prec : IsTrue $ lte n $ length l} ->
                              length (my_take n l) = n
lem_myTake_returns_length_n Z _             = Refl
lem_myTake_returns_length_n (S _) [] {prec} = absurd prec
lem_myTake_returns_length_n (S p) (x :: xs) = cong $ lem_myTake_returns_length_n p xs

||| Drop the first `n` elements of `l`
|||
||| @ n how many elements to drop
||| @ l the list to drop them from
||| @ prec a proof that there are at least `n` elements in `l`
my_drop : (n : Nat) -> (l : List a) -> {auto prec : IsTrue $ lte n $ length l} -> List a
my_drop Z l             = l
my_drop (S _) [] {prec} = absurd prec
my_drop (S p) (x :: xs) = my_drop p xs

||| Proof that my_drop always returns `(length l) - n` elements
|||
lem_myDrop_returns_correct_length : (n : Nat) -> (l : List a) -> {auto prec : IsTrue $ lte n $ length l} ->
                                    n + length (my_drop n l) = length l
lem_myDrop_returns_correct_length Z l = Refl
lem_myDrop_returns_correct_length (S _) [] {prec} = absurd prec
lem_myDrop_returns_correct_length (S p) (x :: xs) = cong $ lem_myDrop_returns_correct_length p xs 

||| Proof that my_take l ++ my_drop l = l
|||
lem_myTakePPmyDrop_eq : (n : Nat) -> (l : List a) -> {auto prec : IsTrue $ lte n $ length l} ->
                        (my_take n l) ++ (my_drop n l) = l
lem_myTakePPmyDrop_eq Z l = Refl
lem_myTakePPmyDrop_eq (S _) [] {prec} = absurd prec
lem_myTakePPmyDrop_eq (S p) (x :: xs) = cong $ lem_myTakePPmyDrop_eq p xs


-------------------------------------------------------------------------------
-- Searching with a predicate
--------------------------------------------------------------------------------


||| Find the first element of a list, `l`, that satisfies a predicate, or `Nothing` if none do.
|||   Return an index, `i`, a value, `v`, a proof that `i` is in bounds & a proof that `(index l i) = v`
|||
||| @ p the predicate
||| @ l the list to search
my_findM : (p : a -> Bool) -> (l : List a) 
          -> Maybe (i : Nat ** v : a ** pib : MyInBounds l i ** my_index i l {prec=pib} = v)
my_findM _ [] = Nothing
my_findM p (x :: xs) with (p x)
  my_findM p (x :: xs) | False with (my_findM p xs)
    my_findM p (x :: xs) | False | Nothing = Nothing
    my_findM p (x :: xs) | False | (Just (i ** v ** p1 ** p2)) = Just $ ((S i) ** v ** p1 ** p2)
  my_findM p (x :: xs) | True = Just $ (Z ** x ** ItsTrue ** Refl)

||| Find the first element of a list that satisfies a predicate, or `Nothing` if none do.
my_find : (a -> Bool) -> List a -> Maybe a
my_find p l with (my_findM p l)
  my_find p l | Nothing = Nothing
  my_find p l | (Just (_ ** v ** _ ** _)) = Just v


-- Alternate implementation with a non-dependent pair for first two components
--   Didn't work out because the recursive call had "No such variable p" (for unknown reasons)
{-
my_findM2 : (p : a -> Bool) -> (l : List a) 
          -> Maybe (rp : (Nat, a) ** let (i, v) = rp in (pIB : (MyInBounds l i) ** (my_index i l {prec=pIB} = v)))
my_findM2 p [] = Nothing
my_findM2 p (x :: xs) with (p x)
  my_findM2 p (x :: xs) | False with (my_findM2 p xs)
    my_findM2 p (x :: xs) | False | wpat = ?h
    my_findM2 p (x :: xs) | False | Nothing = Nothing
    my_findM2 p (x :: xs) | False | (Just y) = ?op_rhs_1_rhs_1
  my_findM2 p (x :: xs) | True = Just $ ((Z, x) ** ItsTrue ** Refl)
-}

||| Find the index of the first element of a list that satisfies a predicate, or
||| `Nothing` if none do.
my_findIndex : (a -> Bool) -> List a -> Maybe Nat
my_findIndex p l with (my_findM p l)
  my_findIndex p l | Nothing = Nothing
  my_findIndex p l | (Just (i ** _ ** _ ** _)) = Just i


||| Proof that if my_findIndex yields `Just i` then `i` is in bounds
my_findIndex_isInBounds : (p : a -> Bool) -> (l : List a) -> (my_findIndex p l = Just i) -> MyInBounds l i
my_findIndex_isInBounds p l prf with (my_findM p l)
  my_findIndex_isInBounds p l prf | Nothing = absurd prf
  my_findIndex_isInBounds p l Refl | (Just (i ** v ** p1 ** p2)) = p1

||| Find the index of the first element of a list that satisfies a predicate, or
||| `Nothing` if none do; return a pair of the index and a proof that it's in bounds
my_findIndex2 : (a -> Bool) -> (l : List a) -> Maybe (i : Nat ** MyInBounds l i)
my_findIndex2 p l with (my_findM p l)
  my_findIndex2 p l | Nothing = Nothing
  my_findIndex2 p l | (Just (i ** _ ** pIB ** _)) = Just (i ** pIB)


-------------------------------------------------------------------------------
-- findIndex with a refinement type
--------------------------------------------------------------------------------

||| Return a function that finds index of the first element of a list that satisfies a predicate, or
||| `Nothing` if none do; such that it's correct
my_findIndexR : TRefine ((a -> Bool) -> List a -> Maybe Nat) 
                        (\f => (p : a -> Bool) -> (l : List a) -> (f p l = Just i) -> MyInBounds l i)
my_findIndexR = (my_findIndex ** my_findIndex_isInBounds)

-------------------------------------------------------------------------------
-- Elem & Remove
--------------------------------------------------------------------------------

my_elem : Eq a => (v : a) -> (l : List a) -> Maybe $ TRefine Nat (MyInBounds l)
my_elem v l = my_findIndex2 (==v) l

my_remove : (l : List a) -> (i : Nat) -> {auto prec : MyInBounds l i} -> List a
my_remove [] i {prec = prec} = absurd prec
my_remove (_ :: xs) Z {prec = _} = xs
my_remove (x :: xs) (S p) = x :: my_remove xs p {prec=?h}
-- In this last clause, the precondition, even though not explicit, flows into the call.


--+-------------------------------------------
--+  Example: Elem & Remove
--+ ------------------------------------------

Vl1 : List Nat
Vl1 = [3, 7, 42, 1]

Vl2 : Maybe (i : Nat ** MyInBounds Vl1 i)
Vl2 = my_elem 7 Vl1
-- Note: be careful with lowercase variables: "vl1" used above fails. Why?

Vl3 : List Nat
Vl3 with (Vl2)
  Vl3 | Nothing = []
  Vl3 | (Just (i ** prf)) = my_remove Vl1 i


--+-------------------------------------------
--+  Variations on remove
--+ ------------------------------------------

my_remove2 : (l : List a) -> TRefine Nat (MyInBounds l) -> List a
my_remove2 [] (_ ** prec) = absurd prec
-- Idris won't split i in the next, so did it manually
  -- my_remove2 (x :: xs) (i ** prec) = ?my_remove2_rhs_1
my_remove2 (_ :: xs) (Z ** _) = xs
my_remove2 (x :: xs) (S p ** prec) = x :: my_remove2 xs (p ** prec)
  -- given: prec : (\i => MyInBounds (x :: xs) i) (S p)
  -- goal :        (\i => IsTrue (lte (S i) (length xs))) p

-- Here Idris will case-split on i in the with clause and it goes through.
--    Note, however, that the earlier "i" is not rewritten (although it exists in the context).
my_remove2a : (l : List a) -> TRefine Nat (MyInBounds l) -> List a
my_remove2a [] (_ ** prec) = absurd prec
my_remove2a (x :: xs) (i ** prec) with (i)
  my_remove2a (x :: xs) (i ** prec) | Z = xs
  my_remove2a (x :: xs) (i ** prec) | (S p) = x :: my_remove2a xs  (p ** prec)


-------------------------------------------------------------------------------
-- IsIn & RemoveV
--------------------------------------------------------------------------------

isIn : Eq a => (v : a) -> (l : List a) -> Bool
isIn v [] = False
isIn v (x :: xs) = (x == v) || isIn v xs

my_removeV : Eq a => (l : List a) -> (v : a) -> {auto prec : IsTrue $ isIn v l} -> List a
my_removeV [] v {prec} = absurd prec
my_removeV (x :: xs) v with (x == v)
  my_removeV (x :: xs) v | False = my_removeV xs v
  -- Above, Idris managed to reason that (x==v)=False 
  -- and, so, could reduce `prec` to what was needed for the recursive call
  my_removeV (x :: xs) v | True = xs



--------------------------------------------------------------------------------
-- Zips 
--------------------------------------------------------------------------------

||| Combine two lists of equal length elementwise using some function. 
|||
||| @ f the function to combine elements with
||| @ l the first list
||| @ r the second list
||| @ prec a proof that the lengths are equal
my_zipWith : (f : a -> b -> c) -> (l : List a) -> (r : List b) -> (prec : IsTrue ((length l) == (length r))) -> List c
my_zipWith f [] [] ItsTrue = []
my_zipWith f [] (x :: xs) prec = absurd prec
my_zipWith f (x :: xs) [] prec = absurd prec
my_zipWith f (x :: xs) (y :: ys) prec = f x y :: my_zipWith f xs ys prec
-- context has: prec : IsTrue (length (x :: xs) == length (y :: ys))
-- needed prec is    : IsTrue (length xs == length ys)
-- and Idris is able to reduce the first to the second by using definitions of length and ==
-- which does not work if Id is used:
my_zipWith2 : (f : a -> b -> c) -> (l : List a) -> (r : List b) -> (prec : (length l) = (length r)) -> List c
my_zipWith2 f [] [] Refl = []
my_zipWith2 f [] (x :: xs) prec = absurd prec
my_zipWith2 f (x :: xs) [] prec = absurd prec
my_zipWith2 f (x :: xs) (y :: ys) prec = f x y :: my_zipWith2 f xs ys (succInjective _ _ prec)


--------------------------------------------------------------------------------
-- Junk
--------------------------------------------------------------------------------

{-
||| Get the tail of a non-empty list and yield the length
||| @ l the list 
||| @ prec proof that the list is non-empty
my_tail2 : (l : List a) -> {auto prec: MyNonEmpty l} -> (l' : List a ** i' : Nat ** i' = length l')
my_tail2 [] {prec = Refl} impossible
my_tail2 (x :: xs) {prec = prec} = (xs ** ?h ** ?my_tail2_rhs_3)
-}

-- Not used

data NatST : (P : Nat -> Type) -> Type -> Type where
  NSTZ : (P : Nat -> Type) -> NatST P (P Z)
  NSTS : (P : Nat -> Type) -> (p : Nat) -> NatST P (P p) -> NatST P (P (S p))

