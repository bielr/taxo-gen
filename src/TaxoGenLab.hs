{-# language DeriveFunctor #-}
{-# language FlexibleInstances #-}
{-# language RebindableSyntax #-}
{-# language TypeFamilies #-}
module TaxoGenLab where

import Prelude hiding (Functor(..), Applicative(..), Monad(..), sequence, (=<<), mapM, mapM_)
import qualified Prelude
import Prob
import Util
import qualified TaxoGen

import GHC.Exts (IsList(..))

import Debug.Trace

import Control.Lens (ix, (.~))
import Control.Monad.State (State, evalState, get, put)

import Data.Function ((&))
import Data.MemoTrie (memo, memo2)
import Data.MultiSet (MultiSet)
import qualified Data.MultiSet as MultiSet
import Data.List.NonEmpty (NonEmpty(..))


data Taxo a = Branch !Height !(MultiSet (Taxo a)) | Leaf !a
    deriving (Eq, Ord)

foldTaxo :: (a -> a -> a) -> Taxo a -> a
foldTaxo _ (Leaf a)       = a
foldTaxo f (Branch h dds) = foldr f (foldTaxo f d) (map (foldTaxo f) ds)
  where
    (d:ds) = MultiSet.toList dds

unlabeled :: Taxo a -> TaxoGen.Taxo
unlabeled (Leaf _)      = TaxoGen.chain 0
unlabeled (Branch h ds) = TaxoGen.Taxo h (MultiSet.fromList (map unlabeled (MultiSet.toList ds)))

newick :: Show a => Taxo a -> String
newick (Leaf a)               = show a
newick (Branch _ descendants) = "(" ++ unwords (map newick (MultiSet.toList descendants)) ++ ")"

instance Show a => Show (Taxo a) where
    show = newick

instance (Ord a, Show a) => TaxoLike (Taxo a) where
    type Label (Taxo a) = a

    relabel labels taxo = evalState (go taxo) labels
      where
        getLabel :: State (Stream a) a
        getLabel = do
            Stream a s <- get
            put s
            return a

        go (Branch h ds) = fmap (Branch h . MultiSet.fromList) (mapM go (MultiSet.toList ds))
        go (Leaf a) = do
            a' <- getLabel
            return (Leaf a')

    rootJoin (t@(Leaf _)     :| ts) = Branch    1  (MultiSet.fromList (t:ts))
    rootJoin (t@(Branch h _) :| ts) = Branch (h+1) (MultiSet.fromList (t:ts))


chain :: Height -> a -> Taxo a
chain 0 a = Leaf a
chain h a = Branch h (MultiSet.singleton (chain (h-1) a))

addChain :: Ord a => a -> Taxo a -> Taxo a
addChain a (Leaf _)               = error "cannot add chain to leaf"
addChain a (Branch h descendants) = Branch h (MultiSet.insert (chain (h-1) a) descendants)

deleteLeaf :: Ord a => a -> Taxo a -> Taxo a
deleteLeaf a t =
    case rec t of
      Just t' -> t'
      Nothing -> error "deleteLeaf: got empty tree"
  where
    rec l@(Leaf a')   = if a == a' then Nothing else Just l
    rec (Branch h ds) =
      case go (MultiSet.toList ds) of
        Nothing -> Nothing
        Just [] -> Nothing
        Just ds -> Just (Branch h (MultiSet.fromList ds))

    go []     = Just []
    go (d:ds) =
      case rec d of
        Just d' -> fmap (d':) (go ds)
        Nothing -> Just ds


deleteLastLeaf :: Ord a => Taxo a -> Taxo a
deleteLastLeaf t = deleteLeaf (foldTaxo max t) t


addRandomChainWeighted :: (Show a, Ord a) => Prob Depth -> a -> Taxo a -> Prob (Taxo a)
addRandomChainWeighted pdepth a taxo = do
    depth <- pdepth
    navigateAndInsert depth taxo
  where
    navigateAndInsert 0     taxo                   = return (addChain a taxo)
    navigateAndInsert depth (Branch h descendants) = do
      let ndesc = MultiSet.size descendants
      i <- uniformlySorted [0..ndesc-1]

      let descList = MultiSet.toAscList descendants
      modifiedDescendant <- navigateAndInsert (depth-1) (descList !! i)

      let descendants' = MultiSet.fromList (descList & ix i .~ modifiedDescendant)
      return (Branch h descendants')

addingLeavesWeighted :: Int -> Height -> Prob Depth -> Prob (Taxo Int)
addingLeavesWeighted width height pdepth =
    case width of
      0 -> return (Branch 0 MultiSet.empty)
      1 -> return (fst start)
      _ -> fmap fst $ iterate (>>= next) (return start) !! (width-2) |>>=| next
  where
    start = (chain height 0, 1)

    next :: (Taxo Int, Int) -> Prob (Taxo Int, Int)
    next (taxo, n) = do
      taxo' <- addRandomChainWeighted pdepth n taxo
      return (taxo', n+1)

addingLeavesProbWeighted :: Int -> Prob Depth -> Prob (Taxo Int)
addingLeavesProbWeighted width pdepth =
    addingLeavesWeighted width height pdepth
  where
    height = maximum (eventValues pdepth) + 1

coalescentForest :: Int -> Height -> Prob [Maybe (Taxo Int)]
coalescentForest = memo2 $ \w h ->
    case h of
      1 -> return [Just (Leaf i) | i <- [0..w-1]]
      _ -> do
        prev <- coalescentForest w (h-1)
        parts <- randomAssignmentFibres w [0..w-1]
        let trees = map (mkTree (h-1) prev) parts
        return trees
  where
    mkTree :: Height -> [Maybe (Taxo Int)] -> [Int] -> Maybe (Taxo Int)
    mkTree h prev part =
        case [t | i <- part, Just t <- [prev!!i]] of
          [] -> Nothing
          ds -> Just (Branch h (MultiSet.fromList ds))

coalescent :: Int -> Height -> Prob (Taxo Int)
coalescent w h = fmap (relabel nats . joinForest) (coalescentForest w h)
  where
    nats = iterStream succ 0
    joinForest forest =
        case [t | Just t <- forest] of
            [] -> undefined
            ts -> Branch h (MultiSet.fromList ts)

coalescentForestMonotone :: Int -> Height -> Prob [Taxo Int]
coalescentForestMonotone = memo2 $ \w h ->
    case h of
      1 -> return [Leaf i | i <- [0..w-1]]
      _ -> do
        prev <- coalescentForestMonotone w (h-1)
        parts <- randomPartitionMonotone [0..length prev-1]

        let partSubtree part = Branch (h-1) (MultiSet.fromList [prev !! i | i <- part])
        return (map partSubtree parts)

coalescentMonotone :: Int -> Height -> Prob (Taxo Int)
coalescentMonotone w h =
    fmap (Branch h . MultiSet.fromList) (coalescentForestMonotone w h)
