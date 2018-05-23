{-# language BangPatterns #-}
{-# language DefaultSignatures #-}
{-# language FlexibleContexts #-}
{-# language RebindableSyntax #-}
{-# language TypeFamilies #-}
module Util where

import Prelude hiding (Functor(..), Applicative(..), Monad(..), sequence, (=<<), mapM, mapM_)
import qualified Prelude
import Prob

import Data.Function (on)
import Data.Kind (Type)
import Data.List (groupBy, sortBy, subsequences)
import Data.List.NonEmpty (NonEmpty)
import qualified Data.List.NonEmpty as NonEmpty
import Data.MemoTrie (HasTrie, memo, memo2)
import Data.MultiSet (MultiSet)
import qualified Data.MultiSet as MultiSet
import Data.Traversable (traverse)


traverseMultiSet :: (Prelude.Applicative f, Ord a, Ord b) => (a -> f b) -> MultiSet a -> f (MultiSet b)
traverseMultiSet f = Prelude.fmap MultiSet.fromList . traverse f . MultiSet.toList


intPartitionsFixed :: Int -> Int -> [[Int]]
intPartitionsFixed l n = go l n n
  where
    go :: Int -> Int -> Int -> [[Int]]
    go !_ 0 !_ = []
    go 1  n  m = if n <= m then [[n]] else []
    go l  n  m = [k:part | k <- [1..min n m], part <- go (l-1) (n-k) k]

randomPartitionFixing :: Int -> Prob [Int]
randomPartitionFixing = memo $ \n -> do
  l <- uniformlySorted [1..n]
  uniformlySorted (intPartitionsFixed l n)

intPartitions :: Int -> [[Int]]
intPartitions n = go n n
  where
    go :: Int -> Int -> [[Int]]
    go 0 _ = [[]]
    go n m = [k:part | k <- [1..min n m], part <- go (n-k) k]

randomPartitionUnif :: Int -> Prob [Int]
randomPartitionUnif = memo (uniformlySorted . intPartitions)

numIntPartitionsFixed :: Int -> Int -> Int
numIntPartitionsFixed = memo2 p
  where
    p 0 0 = 1
    p l n
      | n <= 0 || l <= 0 = 0
      | otherwise        = numIntPartitionsFixed l (n-l) + numIntPartitionsFixed (l-1) (n-1)

numIntPartitions :: Int -> Int
numIntPartitions = memo p
  where
    p !n = sum [numIntPartitionsFixed l n | l <- [1..n]]


randomAssignment :: (HasTrie a, Ord a) => Int -> [a] -> Prob [a]
randomAssignment = flip $ memo $ \codomain ->
    let distrib = uniformlySorted codomain
        cache   = iterate (liftA2 (:) distrib) (return [])
    in  \domLen -> cache !! domLen

fibres :: Ord a => [a] -> [a] -> [[Int]]
fibres codomain img = [[i | (i, a') <- zip [0..] img, a == a'] | a <- codomain]

randomAssignmentFibres :: (HasTrie a, Ord a) => Int -> [a] -> Prob [[Int]]
randomAssignmentFibres = memo2 $ \domLen codomain ->
    fmap (fibres codomain) (randomAssignment domLen codomain)

randomPartitionMonotone :: Ord a => [a] -> Prob [[a]]
randomPartitionMonotone to =
    let parts = map sepsToPartition $ subsequences [1..length to-1]
    in  uniformly parts
  where
    sepsToPartition = go to
      where
        go as []     = [as]
        go as (i:is) =
          let (as', bs) = splitAt i as
          in  as' : go bs (map (subtract i) is)


type Depth = Int
type Height = Int

data Stream a = Stream !a (Stream a)

iterStream :: (a -> a) -> a -> Stream a
iterStream f a = Stream a (iterStream f (f a))

class (Ord (Label taxo), Ord taxo, Show taxo) => TaxoLike taxo where
    {-# minimal rootJoin, relabel #-}

    type Label taxo :: Type
    relabel :: Stream (Label taxo) -> taxo -> taxo

    rootJoin :: NonEmpty taxo -> taxo

    liftRootJoin :: NonEmpty (Prob taxo) -> Prob taxo
    liftRootJoin = fmap rootJoin . sequence1

markovianEqns :: (TaxoLike taxo, Label taxo ~ Int)
              => [NonEmpty Int]
              -> (Int -> Height -> Prob taxo)
              -> Int
              -> Height
              -> [(QQ, [(NonEmpty Int, QQ)])]
markovianEqns parts model w h =
    let joins = map (fmap (relabel nats) . liftRootJoin . NonEmpty.map modelSubtree) parts
    in  [ (pt, [(part, probOf (==t) modelTreeJoin) | (part, modelTreeJoin) <- zip parts joins])
        | Event t pt <- events modelTree
        ]
  where
    nats = iterStream (1+) 0
    modelTree = fmap (relabel nats) (model w h)
    modelSubtree w' = model w' (h-1)
