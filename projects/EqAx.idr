module PLib.EqAx

%access public export
%default total


--------------------------------------------------------------------------------
-- EqAx: Eq extended to include properties (refl, sym, trans)
--------------------------------------------------------------------------------


||| The EqAx: Extend Eq to include properties
interface Eq ty => EqAx ty where
  refl  : (x : ty) -> (x == x) = True
  sym   : {x, y : ty} -> (x == y) = True -> (y == x) = True
  trans : {x, y, z : ty} -> (x == y) = True -> (y == z) = True -> (x == z) = True

--+-------------------------------------------
--+  Examples: EqAx for () and Nat
--+ ------------------------------------------

namespace EqAxImpls

  EqAx () where
    refl () = Refl
    sym {x = ()} {y = ()} _ = Refl
    trans {x = ()} {y = ()} {z = ()} _ _ = Refl

  EqAx Nat where
    refl Z = Refl
    refl (S k) = refl k

    sym {x = Z} {y = Z} _ = Refl
    sym {x = Z} {y = (S k)} prf = absurd prf
    sym {x = (S k)} {y = Z} prf = absurd prf
    sym {x = (S k)} {y = (S j)} prf = sym {x=k} {y=j} prf

    trans {x = Z} {y = Z} {z = Z} pxy pyz = Refl
    trans {x = Z} {y = Z} {z = (S k)} pxy pyz = absurd pyz
    trans {x = Z} {y = (S k)} {z = _} pxy pyz = absurd pxy
    trans {x = (S k)} {y = Z} {z = _} pxy pyz = absurd pxy
    trans {x = (S k)} {y = (S j)} {z = Z} pxy pyz = absurd pyz
    trans {x = (S k)} {y = (S j)} {z = (S i)} pxy pyz = trans {x=k} {y=j} {z=i} pxy pyz


--------------------------------------------------------------------------------
-- EqId: An interface for types whose Eq is equivalent to Id
--------------------------------------------------------------------------------

||| The EqId: Extend Eq to prove that it is equivalent to the Id type
interface Eq ty => EqId ty where
  eq2id : (x, y : ty) -> (x == y) = True -> x = y
  id2eq : (x, y : ty) -> x = y -> (x == y) = True


--+-------------------------------------------
--+  Examples: EqId for (), Bool and Nat
--+ ------------------------------------------

EqId () where
  eq2id () () _ = Refl
  id2eq () () _ = Refl

EqId Bool where
  eq2id False False _  = Refl
  eq2id False True prf = absurd prf
  eq2id True False prf = absurd prf
  eq2id True True   _  = Refl

  id2eq False False prf = Refl
  id2eq False True prf  = absurd prf
  id2eq True False prf  = absurd prf
  id2eq True True prf   = Refl

EqId Nat where
  eq2id Z Z _ = Refl
  eq2id Z (S k) prf = absurd prf
  eq2id (S k) Z prf = absurd prf
  eq2id (S k) (S j) prf = cong $ eq2id k j prf
  id2eq Z Z Refl = Refl
  id2eq Z (S k) prf = absurd prf
  id2eq (S k) Z prf = absurd prf
  id2eq (S k) (S j) prf = id2eq k j (succInjective _ _ prf)

(EqId a, EqId b) => EqId (Either a b) where
  eq2id (Left lx) (Left ly) prf   = cong $ eq2id lx ly prf
  eq2id (Left _) (Right _) prf    = absurd prf
  eq2id (Right _) (Left _) prf    = absurd prf
  eq2id (Right rx) (Right ry) prf = cong $ eq2id rx ry prf

  id2eq (Left v) (Left v) Refl   = id2eq v v Refl
  id2eq (Left _) (Right _) Refl    impossible
  id2eq (Right _) (Left _) Refl    impossible
  id2eq (Right v) (Right v) Refl = id2eq v v Refl


--------------------------------------------------------------------------------
-- BitStr with Eq, but NOT EqId because 001 == 1 but not 001 = 1
--------------------------------------------------------------------------------

data BitStr : Type where
  BSe : BitStr
  BS0 : BitStr -> BitStr
  BS1 : BitStr -> BitStr

Eq BitStr where
  (==) BSe BSe = True
  (==) (BS1 x) (BS1 y) = x == y
  (==) BSe (BS1 y)     = False
  (==) (BS1 x) BSe     = False
  (==) x (BS0 y)       = x == y
  (==) (BS0 x) y       = x == y

note_BS1: BSe == (BS0 BSe) = True
note_BS1 = Refl

note_BS2: Not (BSe = (BS0 BSe))
note_BS2 Refl impossible


{-
EqId BitStr where
  eq2id BSe BSe _ = Refl
  eq2id BSe (BS0 x) prf = absurd prf
  eq2id BSe (BS1 x) prf = ?EqId_rhs_7
  eq2id (BS0 x) y prf = ?EqId_rhs_4
  eq2id (BS1 x) y prf = ?EqId_rhs_5
  id2eq x y prf = ?EqId_rhs_2
-}


--------------------------------------------------------------------------------
-- A type-class implementation of EqAx given EqId
--------------------------------------------------------------------------------
{-

EqId a => EqAx a where
    refl x = id2eq x x Refl
    sym {x} {y} p with (eq2id x y p)
      sym {x = u} {y = u} p | Refl = id2eq u u Refl
    trans {x} {y} {z} pxy pyz with (eq2id x y pxy)
      trans {x} {y} {z} pxy pyz | qxy with (eq2id y z pyz)
        trans {x = u} {y = u} {z = u} _ _ | Refl | Refl = id2eq u u Refl
-}
 
