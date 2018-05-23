{-# language DeriveFunctor #-}
{-# language FlexibleInstances #-}
{-# language OverloadedLists #-}
{-# language RebindableSyntax #-}
{-# language TypeFamilies #-}
module TaxoGenOrd where

import Prelude hiding (Functor(..), Applicative(..), Monad(..), sequence, (=<<), mapM, mapM_)
import qualified Prelude
import Prob
import Util
import qualified TaxoGenLab

import GHC.Exts (IsList(..))

import Control.Monad.State (State, evalState, get, put)

import Data.List.NonEmpty (NonEmpty(..), (<|))
import qualified Data.List.NonEmpty as NonEmpty
import Data.MemoTrie (memo, memo2)
import qualified Data.MultiSet as MultiSet


data Taxo a = Branch !Height !(NonEmpty (Taxo a)) | Leaf !a
    deriving (Eq, Ord, Prelude.Functor)

foldTaxo :: (a -> a -> a) -> Taxo a -> a
foldTaxo _ (Leaf a)           = a
foldTaxo f (Branch h (d:|ds)) = foldr f (foldTaxo f d) (map (foldTaxo f) ds)

unordered :: Ord a => Taxo a -> TaxoGenLab.Taxo a
unordered (Leaf a)      = TaxoGenLab.Leaf a
unordered (Branch h ds) = TaxoGenLab.Branch h (MultiSet.fromList (map unordered (toList ds)))

newick :: Show a => Taxo a -> String
newick (Leaf a)               = show a
newick (Branch _ descendants) = "(" ++ unwords (map newick (toList descendants)) ++ ")"

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

        go (Branch h ds) = fmap (Branch h) (mapM1 go ds)
        go (Leaf a) = do
            a' <- getLabel
            return (Leaf a')

    rootJoin tts@((Leaf _)     :| _) = Branch    1  tts
    rootJoin tts@((Branch h _) :| _) = Branch (h+1) tts


chain :: Height -> a -> Taxo a
chain 0 a = Leaf a
chain h a = Branch h [chain (h-1) a]

addChain :: a -> Taxo a -> Taxo a
addChain a (Leaf _)               = error "cannot add chain to leaf"
addChain a (Branch h descendants) = Branch h (chain (h-1) a <| descendants)

deleteLeaf :: Ord a => a -> Taxo a -> Taxo a
deleteLeaf a t =
    case rec t of
      Just t' -> t'
      Nothing -> error "deleteLeaf: got empty tree"
  where
    rec l@(Leaf a')   = if a == a' then Nothing else Just l
    rec (Branch h ds) = fmap (Branch h) . NonEmpty.nonEmpty =<< go (NonEmpty.toList ds)

    go []     = Just []
    go (d:ds) =
      case rec d of
        Just d' -> fmap (d':) (go ds)
        Nothing -> Just ds


deleteLastLeaf :: Ord a => Taxo a -> Taxo a
deleteLastLeaf t = deleteLeaf (foldTaxo max t) t


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
        case NonEmpty.nonEmpty [t | i <- part, Just t <- [prev!!i]] of
          Just ds -> Just (Branch h ds)
          Nothing -> Nothing

coalescent :: Int -> Height -> Prob (Taxo Int)
coalescent w h = fmap (relabel nats . joinForest) (coalescentForest w h)
  where
    nats = iterStream succ 0
    joinForest forest =
        case NonEmpty.nonEmpty [t | Just t <- forest] of
            Just ts -> Branch h ts
            Nothing -> undefined

coalescentForestMonotone :: Int -> Height -> Prob [Taxo Int]
coalescentForestMonotone = memo2 $ \w h ->
    case h of
      1 -> return [Leaf i | i <- [0..w-1]]
      _ -> do
        prev <- coalescentForestMonotone w (h-1)
        parts <- randomPartitionMonotone [0..length prev-1]

        let partSubtree part = Branch (h-1) (NonEmpty.fromList [prev !! i | i <- part])
        return (map partSubtree parts)

coalescentMonotone :: Int -> Int -> Prob (Taxo Int)
coalescentMonotone w h =
    fmap (Branch h . NonEmpty.fromList) (coalescentForestMonotone w h)
