{-# LANGUAGE CPP #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE UndecidableInstances #-}
#if __GLASGOW_HASKELL__ >= 702
{-# LANGUAGE Safe #-}
#endif
#if __GLASGOW_HASKELL__ >= 706
{-# LANGUAGE DeriveGeneric #-}
#endif
#if __GLASGOW_HASKELL__ >= 710
{-# LANGUAGE AutoDeriveTypeable #-}
#endif
-----------------------------------------------------------------------------
-- |
-- Module      :  Data.FTFingerTree
-- Copyright   :  (c) Ross Paterson, Ralf Hinze 2006
-- License     :  BSD-style
-- Maintainer  :  R.Paterson@city.ac.uk
-- Stability   :  experimental
-- Portability :  non-portable (MPTCs and functional dependencies)
--
-- A general sequence representation with arbitrary annotations, for
-- use as a base for implementations of various collection types, as
-- described in section 4 of
--
--  * Ralf Hinze and Ross Paterson,
--    \"Finger trees: a simple general-purpose data structure\",
--    /Journal of Functional Programming/ 16:2 (2006) pp 197-217.
--    <http://staff.city.ac.uk/~ross/papers/FTFingerTree.html>
--
-- For a directly usable sequence type, see @Data.Sequence@, which is
-- a specialization of this structure.
--
-- An amortized running time is given for each operation, with /n/
-- referring to the length of the sequence.  These bounds hold even in
-- a persistent (shared) setting.
--
-- /Note/: Many of these operations have the same names as similar
-- operations on lists in the "Prelude".  The ambiguity may be resolved
-- using either qualification or the @hiding@ clause.
--
-----------------------------------------------------------------------------

{-# OPTIONS_GHC -fno-warn-redundant-constraints #-}

module Data.FTFingerTree where

import Prelude hiding (null, reverse)
#if MIN_VERSION_base(4,6,0)
import GHC.Generics
#endif
#if MIN_VERSION_base(4,8,0)
import qualified Prelude (null)
#else
import Control.Applicative (Applicative(pure, (<*>)), (<$>))
import Data.Monoid
import Data.Foldable (Foldable(foldMap))
#endif
#if (MIN_VERSION_base(4,9,0)) && !(MIN_VERSION_base(4,11,0))
import Data.Semigroup
#endif
import Data.Foldable (toList)

infixr 5 ><
infixr 5 <|, :<
infixl 5 |>, :>

-- | View of the left end of a sequence.
data ViewL s t a b where
    EmptyL :: ViewL s t a a       -- ^ empty sequence
    (:<) :: t a x -> s x b -> ViewL s t a b      -- ^ leftmost element and the rest of the sequence

-- | View of the right end of a sequence.
data ViewR s t a b where
    EmptyR :: ViewR s t a a        -- ^ empty sequence
    (:>) :: s a x -> t x b -> ViewR s t a b      -- ^ the sequence minus the rightmost element,
                    -- and the rightmost element

-- Explicit Digit type (Exercise 1)

data Digit t a b where
    One :: t a b -> Digit t a b
    Two :: t a b -> t b c -> Digit t a c
    Three :: t a b -> t b c -> t c d -> Digit t a d
    Four :: t a b -> t b c -> t c d -> t d e -> Digit t a e

-------------------
-- 4.1 Measurements
-------------------

-- | Things that can be measured.
class (Monoid v) => Measured v t | t -> v where
    measure :: t a b -> v

---------------------------
-- 4.2 Caching measurements
---------------------------

data Node v t a b where
    Node2 :: !v -> t a b -> t b c -> Node v t a c
    Node3 :: !v -> t a b -> t b c -> t c d -> Node v t a d

node2        ::  (Measured v t) => t a b -> t b c -> Node v t a c
node2 a b    =   Node2 (measure a `mappend` measure b) a b

node3        ::  (Measured v t) => t a b -> t b c -> t c d -> Node v t a d
node3 a b c  =   Node3 (measure a `mappend` measure b `mappend` measure c) a b c

instance (Monoid v) => Measured v (Node v a) where
    measure (Node2 v _ _)    =  v
    measure (Node3 v _ _ _)  =  v

nodeToDigit :: Node v t a b -> Digit t a b
nodeToDigit (Node2 _ a b) = Two a b
nodeToDigit (Node3 _ a b c) = Three a b c

-- | A representation of a sequence of values of type @a@, allowing
-- access to the ends in constant time, and append and split in time
-- logarithmic in the size of the smaller piece.
--
-- The collection is also parameterized by a measure type @v@, which
-- is used to specify a position in the sequence for the 'split' operation.
-- The types of the operations enforce the constraint @'Measured' v a@,
-- which also implies that the type @v@ is determined by @a@.
--
-- A variety of abstract data types can be implemented by using different
-- element types and measurements.
data FTFingerTree v t a b where
    Empty :: FTFingerTree v t a a
    Single :: t a b -> FTFingerTree v t a b
    Deep :: !v -> !(Digit t a b) -> FTFingerTree v (Node v t) b c -> !(Digit t c d) -> FTFingerTree v t a d

deep ::  (Measured v t) =>
     Digit t a b -> FTFingerTree v (Node v t) b c -> Digit t c d -> FTFingerTree v t a d
deep pr m sf =
    Deep ((measure pr `mappend` measure m) `mappend` measure sf) pr m sf

-- | /O(1)/. The cached measure of a tree.
instance (Measured v a) => Measured v (FTFingerTree v a) where
    measure Empty           =  mempty
    measure (Single x)      =  measure x
    measure (Deep v _ _ _)  =  v

instance (Measured v a) => Measured v (Digit a) where
    measure = undefined

-----------------------------------------------------
-- 4.3 Construction, deconstruction and concatenation
-----------------------------------------------------

-- | /O(1)/. The empty sequence.
-- TODO(sandy): should this be to/from void?
empty :: Measured v t => FTFingerTree v t a a
empty = Empty

-- | /O(1)/. A singleton sequence.
singleton :: Measured v t => t a b -> FTFingerTree v t a b
singleton = Single

-- | /O(1)/. Add an element to the left end of a sequence.
-- Mnemonic: a triangle with the single element at the pointy end.
(<|) :: (Measured v t) => t a b -> FTFingerTree v t b c -> FTFingerTree v t a c
a <| Empty              =  Single a
a <| Single b           =  deep (One a) Empty (One b)
a <| Deep v (Four b c d e) m sf = m `seq`
    Deep (measure a `mappend` v) (Two a b) (node3 c d e <| m) sf
a <| Deep v pr m sf     =
    Deep (measure a `mappend` v) (consDigit a pr) m sf

consDigit :: t a b -> Digit t b c -> Digit t a c
consDigit a (One b) = Two a b
consDigit a (Two b c) = Three a b c
consDigit a (Three b c d) = Four a b c d
consDigit _ (Four _ _ _ _) = illegal_argument "consDigit"

-- | /O(1)/. Add an element to the right end of a sequence.
-- Mnemonic: a triangle with the single element at the pointy end.
(|>) :: (Measured v t) => FTFingerTree v t a b -> t b c -> FTFingerTree v t a c
Empty |> a              =  Single a
Single a |> b           =  deep (One a) Empty (One b)
Deep v pr m (Four a b c d) |> e = m `seq`
    Deep (v `mappend` measure e) pr (m |> node3 a b c) (Two d e)
Deep v pr m sf |> x     =
    Deep (v `mappend` measure x) pr m (snocDigit sf x)

snocDigit :: Digit t a b -> t b c -> Digit t a c
snocDigit (One a) b = Two a b
snocDigit (Two a b) c = Three a b c
snocDigit (Three a b c) d = Four a b c d
snocDigit (Four _ _ _ _) _ = illegal_argument "snocDigit"

-- | /O(1)/. Is this the empty sequence?
null :: FTFingerTree v t a b -> Bool
null Empty = True
null _ = False

-- | /O(1)/. Analyse the left end of a sequence.
viewl :: (Measured v t) => FTFingerTree v t a b -> ViewL (FTFingerTree v t) t a b
viewl Empty                     =  EmptyL
viewl (Single x)                =  x :< Empty
viewl (Deep _ (One x) m sf)     =  x :< rotL m sf
viewl (Deep _ pr m sf)          =
  case lconsDigit pr of
    ConsL headDigit tailDigit -> headDigit :< deep tailDigit m sf

rotL
    :: (Measured v t)
    => FTFingerTree v (Node v t) a b
    -> Digit t b c
    -> FTFingerTree v t a c
rotL m sf      =   case viewl m of
    EmptyL  ->  digitToTree sf
    a :< m' ->  Deep (measure m `mappend` measure sf) (nodeToDigit a) m' sf

data ConsL t a b where
  ConsL :: t a x -> Digit t x b -> ConsL t a b

lconsDigit :: Digit t a b -> ConsL t a b
lconsDigit (One a) = illegal_argument "lconsDigit"
lconsDigit (Two a b) = ConsL a $ One b
lconsDigit (Three a b c) = ConsL a $ Two b c
lconsDigit (Four a b c d) = ConsL a $ Three b c d

-- | /O(1)/. Analyse the right end of a sequence.
viewr :: (Measured v t) => FTFingerTree v t a b -> ViewR (FTFingerTree v t) t a b
viewr Empty                     =  EmptyR
viewr (Single x)                =  Empty :> x
viewr (Deep _ pr m (One x))     =  rotR pr m :> x
viewr (Deep _ pr m sf)          =
  case rconsDigit sf of
    ConsR x y -> deep pr m x :> y

rotR :: (Measured v t) => Digit t a b -> FTFingerTree v (Node v t) b c -> FTFingerTree v t a c
rotR pr m = case viewr m of
    EmptyR  ->  digitToTree pr
    m' :> a ->  Deep (measure pr `mappend` measure m) pr m' (nodeToDigit a)

data ConsR t a b where
  ConsR :: Digit t a x -> t x b -> ConsR t a b

rconsDigit :: Digit t a b -> ConsR t a b
rconsDigit (One a) = illegal_argument "rconsDigit"
rconsDigit (Two a b) = ConsR (One a) b
rconsDigit (Three a b c) = ConsR (Two a b) c
rconsDigit (Four a b c d) = ConsR (Three a b c) d

digitToTree :: (Measured v t) => Digit t a b -> FTFingerTree v t a b
digitToTree (One a) = Single a
digitToTree (Two a b) = deep (One a) Empty (One b)
digitToTree (Three a b c) = deep (Two a b) Empty (One c)
digitToTree (Four a b c d) = deep (Two a b) Empty (Two c d)

----------------
-- Concatenation
----------------

-- | /O(log(min(n1,n2)))/. Concatenate two sequences.
(><) :: (Measured v t) => FTFingerTree v t a b -> FTFingerTree v t b c -> FTFingerTree v t a c
(><) =  appendTree0

appendTree0
    :: (Measured v t)
    => FTFingerTree v t a b
    -> FTFingerTree v t b c
    -> FTFingerTree v t a c
appendTree0 Empty xs =
    xs
appendTree0 xs Empty =
    xs
appendTree0 (Single x) xs =
    x <| xs
appendTree0 xs (Single x) =
    xs |> x
appendTree0 (Deep _ pr1 m1 sf1) (Deep _ pr2 m2 sf2) =
    deep pr1 (addDigits0 m1 sf1 pr2 m2) sf2

addDigits0
    :: (Measured v t)
    => FTFingerTree v (Node v t) a b
    -> Digit t b c
    -> Digit t c d
    -> FTFingerTree v (Node v t) d e
    -> FTFingerTree v (Node v t) a e
addDigits0 m1 (One a) (One b) m2 =
    appendTree1 m1 (node2 a b) m2
addDigits0 m1 (One a) (Two b c) m2 =
    appendTree1 m1 (node3 a b c) m2
addDigits0 m1 (One a) (Three b c d) m2 =
    appendTree2 m1 (node2 a b) (node2 c d) m2
addDigits0 m1 (One a) (Four b c d e) m2 =
    appendTree2 m1 (node3 a b c) (node2 d e) m2
addDigits0 m1 (Two a b) (One c) m2 =
    appendTree1 m1 (node3 a b c) m2
addDigits0 m1 (Two a b) (Two c d) m2 =
    appendTree2 m1 (node2 a b) (node2 c d) m2
addDigits0 m1 (Two a b) (Three c d e) m2 =
    appendTree2 m1 (node3 a b c) (node2 d e) m2
addDigits0 m1 (Two a b) (Four c d e f) m2 =
    appendTree2 m1 (node3 a b c) (node3 d e f) m2
addDigits0 m1 (Three a b c) (One d) m2 =
    appendTree2 m1 (node2 a b) (node2 c d) m2
addDigits0 m1 (Three a b c) (Two d e) m2 =
    appendTree2 m1 (node3 a b c) (node2 d e) m2
addDigits0 m1 (Three a b c) (Three d e f) m2 =
    appendTree2 m1 (node3 a b c) (node3 d e f) m2
addDigits0 m1 (Three a b c) (Four d e f g) m2 =
    appendTree3 m1 (node3 a b c) (node2 d e) (node2 f g) m2
addDigits0 m1 (Four a b c d) (One e) m2 =
    appendTree2 m1 (node3 a b c) (node2 d e) m2
addDigits0 m1 (Four a b c d) (Two e f) m2 =
    appendTree2 m1 (node3 a b c) (node3 d e f) m2
addDigits0 m1 (Four a b c d) (Three e f g) m2 =
    appendTree3 m1 (node3 a b c) (node2 d e) (node2 f g) m2
addDigits0 m1 (Four a b c d) (Four e f g h) m2 =
    appendTree3 m1 (node3 a b c) (node3 d e f) (node2 g h) m2

appendTree1
    :: (Measured v t)
    => FTFingerTree v t a b
    -> t b c
    -> FTFingerTree v t c d
    -> FTFingerTree v t a d
appendTree1 Empty a xs =
    a <| xs
appendTree1 xs a Empty =
    xs |> a
appendTree1 (Single x) a xs =
    x <| a <| xs
appendTree1 xs a (Single x) =
    xs |> a |> x
appendTree1 (Deep _ pr1 m1 sf1) a (Deep _ pr2 m2 sf2) =
    deep pr1 (addDigits1 m1 sf1 a pr2 m2) sf2

addDigits1
    :: (Measured v t)
    => FTFingerTree v (Node v t) a b
    -> Digit t b c
    -> t c d
    -> Digit t d e
    -> FTFingerTree v (Node v t) e f
    -> FTFingerTree v (Node v t) a f
addDigits1 m1 (One a) b (One c) m2 =
    appendTree1 m1 (node3 a b c) m2
addDigits1 m1 (One a) b (Two c d) m2 =
    appendTree2 m1 (node2 a b) (node2 c d) m2
addDigits1 m1 (One a) b (Three c d e) m2 =
    appendTree2 m1 (node3 a b c) (node2 d e) m2
addDigits1 m1 (One a) b (Four c d e f) m2 =
    appendTree2 m1 (node3 a b c) (node3 d e f) m2
addDigits1 m1 (Two a b) c (One d) m2 =
    appendTree2 m1 (node2 a b) (node2 c d) m2
addDigits1 m1 (Two a b) c (Two d e) m2 =
    appendTree2 m1 (node3 a b c) (node2 d e) m2
addDigits1 m1 (Two a b) c (Three d e f) m2 =
    appendTree2 m1 (node3 a b c) (node3 d e f) m2
addDigits1 m1 (Two a b) c (Four d e f g) m2 =
    appendTree3 m1 (node3 a b c) (node2 d e) (node2 f g) m2
addDigits1 m1 (Three a b c) d (One e) m2 =
    appendTree2 m1 (node3 a b c) (node2 d e) m2
addDigits1 m1 (Three a b c) d (Two e f) m2 =
    appendTree2 m1 (node3 a b c) (node3 d e f) m2
addDigits1 m1 (Three a b c) d (Three e f g) m2 =
    appendTree3 m1 (node3 a b c) (node2 d e) (node2 f g) m2
addDigits1 m1 (Three a b c) d (Four e f g h) m2 =
    appendTree3 m1 (node3 a b c) (node3 d e f) (node2 g h) m2
addDigits1 m1 (Four a b c d) e (One f) m2 =
    appendTree2 m1 (node3 a b c) (node3 d e f) m2
addDigits1 m1 (Four a b c d) e (Two f g) m2 =
    appendTree3 m1 (node3 a b c) (node2 d e) (node2 f g) m2
addDigits1 m1 (Four a b c d) e (Three f g h) m2 =
    appendTree3 m1 (node3 a b c) (node3 d e f) (node2 g h) m2
addDigits1 m1 (Four a b c d) e (Four f g h i) m2 =
    appendTree3 m1 (node3 a b c) (node3 d e f) (node3 g h i) m2

appendTree2
    :: (Measured v t)
    => FTFingerTree v t a b
    -> t b c
    -> t c d
    -> FTFingerTree v t d e
    -> FTFingerTree v t a e
appendTree2 Empty a b xs =
    a <| b <| xs
appendTree2 xs a b Empty =
    xs |> a |> b
appendTree2 (Single x) a b xs =
    x <| a <| b <| xs
appendTree2 xs a b (Single x) =
    xs |> a |> b |> x
appendTree2 (Deep _ pr1 m1 sf1) a b (Deep _ pr2 m2 sf2) =
    deep pr1 (addDigits2 m1 sf1 a b pr2 m2) sf2

addDigits2
    :: (Measured v t)
    => FTFingerTree v (Node v t) a b
    -> Digit t b c
    -> t c d
    -> t d e
    -> Digit t e f
    -> FTFingerTree v (Node v t) f g
    -> FTFingerTree v (Node v t) a g
addDigits2 m1 (One a) b c (One d) m2 =
    appendTree2 m1 (node2 a b) (node2 c d) m2
addDigits2 m1 (One a) b c (Two d e) m2 =
    appendTree2 m1 (node3 a b c) (node2 d e) m2
addDigits2 m1 (One a) b c (Three d e f) m2 =
    appendTree2 m1 (node3 a b c) (node3 d e f) m2
addDigits2 m1 (One a) b c (Four d e f g) m2 =
    appendTree3 m1 (node3 a b c) (node2 d e) (node2 f g) m2
addDigits2 m1 (Two a b) c d (One e) m2 =
    appendTree2 m1 (node3 a b c) (node2 d e) m2
addDigits2 m1 (Two a b) c d (Two e f) m2 =
    appendTree2 m1 (node3 a b c) (node3 d e f) m2
addDigits2 m1 (Two a b) c d (Three e f g) m2 =
    appendTree3 m1 (node3 a b c) (node2 d e) (node2 f g) m2
addDigits2 m1 (Two a b) c d (Four e f g h) m2 =
    appendTree3 m1 (node3 a b c) (node3 d e f) (node2 g h) m2
addDigits2 m1 (Three a b c) d e (One f) m2 =
    appendTree2 m1 (node3 a b c) (node3 d e f) m2
addDigits2 m1 (Three a b c) d e (Two f g) m2 =
    appendTree3 m1 (node3 a b c) (node2 d e) (node2 f g) m2
addDigits2 m1 (Three a b c) d e (Three f g h) m2 =
    appendTree3 m1 (node3 a b c) (node3 d e f) (node2 g h) m2
addDigits2 m1 (Three a b c) d e (Four f g h i) m2 =
    appendTree3 m1 (node3 a b c) (node3 d e f) (node3 g h i) m2
addDigits2 m1 (Four a b c d) e f (One g) m2 =
    appendTree3 m1 (node3 a b c) (node2 d e) (node2 f g) m2
addDigits2 m1 (Four a b c d) e f (Two g h) m2 =
    appendTree3 m1 (node3 a b c) (node3 d e f) (node2 g h) m2
addDigits2 m1 (Four a b c d) e f (Three g h i) m2 =
    appendTree3 m1 (node3 a b c) (node3 d e f) (node3 g h i) m2
addDigits2 m1 (Four a b c d) e f (Four g h i j) m2 =
    appendTree4 m1 (node3 a b c) (node3 d e f) (node2 g h) (node2 i j) m2

appendTree3 :: (Measured v t) => FTFingerTree v t a b -> t b c -> t c d -> t d e -> FTFingerTree v t e f -> FTFingerTree v t a f
appendTree3 Empty a b c xs =
    a <| b <| c <| xs
appendTree3 xs a b c Empty =
    xs |> a |> b |> c
appendTree3 (Single x) a b c xs =
    x <| a <| b <| c <| xs
appendTree3 xs a b c (Single x) =
    xs |> a |> b |> c |> x
appendTree3 (Deep _ pr1 m1 sf1) a b c (Deep _ pr2 m2 sf2) =
    deep pr1 (addDigits3 m1 sf1 a b c pr2 m2) sf2

addDigits3
    :: (Measured v t)
    => FTFingerTree v (Node v t) a b
    -> Digit t b c
    -> t c d
    -> t d e
    -> t e f
    -> Digit t f g
    -> FTFingerTree v (Node v t) g h
    -> FTFingerTree v (Node v t) a h
addDigits3 m1 (One a) b c d (One e) m2 =
    appendTree2 m1 (node3 a b c) (node2 d e) m2
addDigits3 m1 (One a) b c d (Two e f) m2 =
    appendTree2 m1 (node3 a b c) (node3 d e f) m2
addDigits3 m1 (One a) b c d (Three e f g) m2 =
    appendTree3 m1 (node3 a b c) (node2 d e) (node2 f g) m2
addDigits3 m1 (One a) b c d (Four e f g h) m2 =
    appendTree3 m1 (node3 a b c) (node3 d e f) (node2 g h) m2
addDigits3 m1 (Two a b) c d e (One f) m2 =
    appendTree2 m1 (node3 a b c) (node3 d e f) m2
addDigits3 m1 (Two a b) c d e (Two f g) m2 =
    appendTree3 m1 (node3 a b c) (node2 d e) (node2 f g) m2
addDigits3 m1 (Two a b) c d e (Three f g h) m2 =
    appendTree3 m1 (node3 a b c) (node3 d e f) (node2 g h) m2
addDigits3 m1 (Two a b) c d e (Four f g h i) m2 =
    appendTree3 m1 (node3 a b c) (node3 d e f) (node3 g h i) m2
addDigits3 m1 (Three a b c) d e f (One g) m2 =
    appendTree3 m1 (node3 a b c) (node2 d e) (node2 f g) m2
addDigits3 m1 (Three a b c) d e f (Two g h) m2 =
    appendTree3 m1 (node3 a b c) (node3 d e f) (node2 g h) m2
addDigits3 m1 (Three a b c) d e f (Three g h i) m2 =
    appendTree3 m1 (node3 a b c) (node3 d e f) (node3 g h i) m2
addDigits3 m1 (Three a b c) d e f (Four g h i j) m2 =
    appendTree4 m1 (node3 a b c) (node3 d e f) (node2 g h) (node2 i j) m2
addDigits3 m1 (Four a b c d) e f g (One h) m2 =
    appendTree3 m1 (node3 a b c) (node3 d e f) (node2 g h) m2
addDigits3 m1 (Four a b c d) e f g (Two h i) m2 =
    appendTree3 m1 (node3 a b c) (node3 d e f) (node3 g h i) m2
addDigits3 m1 (Four a b c d) e f g (Three h i j) m2 =
    appendTree4 m1 (node3 a b c) (node3 d e f) (node2 g h) (node2 i j) m2
addDigits3 m1 (Four a b c d) e f g (Four h i j k) m2 =
    appendTree4 m1 (node3 a b c) (node3 d e f) (node3 g h i) (node2 j k) m2

appendTree4
    :: (Measured v t)
    => FTFingerTree v t a b
    -> t b c
    -> t c d
    -> t d e
    -> t e f
    -> FTFingerTree v t f g
    -> FTFingerTree v t a g
appendTree4 Empty a b c d xs =
    a <| b <| c <| d <| xs
appendTree4 xs a b c d Empty =
    xs |> a |> b |> c |> d
appendTree4 (Single x) a b c d xs =
    x <| a <| b <| c <| d <| xs
appendTree4 xs a b c d (Single x) =
    xs |> a |> b |> c |> d |> x
appendTree4 (Deep _ pr1 m1 sf1) a b c d (Deep _ pr2 m2 sf2) =
    deep pr1 (addDigits4 m1 sf1 a b c d pr2 m2) sf2

addDigits4
    :: (Measured v t)
    => FTFingerTree v (Node v t) a b
    -> Digit t b c
    -> t c d
    -> t d e
    -> t e f
    -> t f g
    -> Digit t g h
    -> FTFingerTree v (Node v t) h i
    -> FTFingerTree v (Node v t) a i
addDigits4 m1 (One a) b c d e (One f) m2 =
    appendTree2 m1 (node3 a b c) (node3 d e f) m2
addDigits4 m1 (One a) b c d e (Two f g) m2 =
    appendTree3 m1 (node3 a b c) (node2 d e) (node2 f g) m2
addDigits4 m1 (One a) b c d e (Three f g h) m2 =
    appendTree3 m1 (node3 a b c) (node3 d e f) (node2 g h) m2
addDigits4 m1 (One a) b c d e (Four f g h i) m2 =
    appendTree3 m1 (node3 a b c) (node3 d e f) (node3 g h i) m2
addDigits4 m1 (Two a b) c d e f (One g) m2 =
    appendTree3 m1 (node3 a b c) (node2 d e) (node2 f g) m2
addDigits4 m1 (Two a b) c d e f (Two g h) m2 =
    appendTree3 m1 (node3 a b c) (node3 d e f) (node2 g h) m2
addDigits4 m1 (Two a b) c d e f (Three g h i) m2 =
    appendTree3 m1 (node3 a b c) (node3 d e f) (node3 g h i) m2
addDigits4 m1 (Two a b) c d e f (Four g h i j) m2 =
    appendTree4 m1 (node3 a b c) (node3 d e f) (node2 g h) (node2 i j) m2
addDigits4 m1 (Three a b c) d e f g (One h) m2 =
    appendTree3 m1 (node3 a b c) (node3 d e f) (node2 g h) m2
addDigits4 m1 (Three a b c) d e f g (Two h i) m2 =
    appendTree3 m1 (node3 a b c) (node3 d e f) (node3 g h i) m2
addDigits4 m1 (Three a b c) d e f g (Three h i j) m2 =
    appendTree4 m1 (node3 a b c) (node3 d e f) (node2 g h) (node2 i j) m2
addDigits4 m1 (Three a b c) d e f g (Four h i j k) m2 =
    appendTree4 m1 (node3 a b c) (node3 d e f) (node3 g h i) (node2 j k) m2
addDigits4 m1 (Four a b c d) e f g h (One i) m2 =
    appendTree3 m1 (node3 a b c) (node3 d e f) (node3 g h i) m2
addDigits4 m1 (Four a b c d) e f g h (Two i j) m2 =
    appendTree4 m1 (node3 a b c) (node3 d e f) (node2 g h) (node2 i j) m2
addDigits4 m1 (Four a b c d) e f g h (Three i j k) m2 =
    appendTree4 m1 (node3 a b c) (node3 d e f) (node3 g h i) (node2 j k) m2
addDigits4 m1 (Four a b c d) e f g h (Four i j k l) m2 =
    appendTree4 m1 (node3 a b c) (node3 d e f) (node3 g h i) (node3 j k l) m2

illegal_argument :: String -> a
illegal_argument name =
    error $ "Logic error: " ++ name ++ " called with illegal argument"
