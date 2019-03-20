{-# language BangPatterns #-}
{-# language FlexibleContexts #-}
{-# language RankNTypes #-}
{-# language RebindableSyntax #-}
{-# language TypeApplications #-}
{-# language TypeFamilies #-}
module TaxoGen where

import Prelude hiding (Functor(..), Applicative(..), Monad(..), sequence, (=<<), mapM, mapM_)
import qualified Prelude
import Prob
import Util

import Control.Exception (assert)
import Control.Lens

import Data.Coerce (Coercible, coerce)
import Data.List (groupBy, sort, sortBy)
import Data.List.NonEmpty (NonEmpty(..))
import qualified Data.List.NonEmpty as NonEmpty
import Data.MemoTrie (memo, memo2)
import Data.MultiSet (MultiSet)
import qualified Data.MultiSet as MultiSet
import qualified Data.Random                          as R
import qualified Data.Random.Distribution.Categorical as R
import Data.Traversable (for)


data Taxo = Taxo !Height !(MultiSet Taxo)
  deriving (Eq, Ord)


newick :: Taxo -> String
newick (Taxo _ descendants)
  | MultiSet.null descendants = "*"
  | otherwise                 = "(" ++ unwords (map newick (MultiSet.toList descendants)) ++ ")"

instance Show Taxo where
    show = newick

addDescendant :: Taxo -> Taxo -> Taxo
addDescendant taxo (Taxo h desc) = Taxo h (MultiSet.insert taxo desc)

instance TaxoLike Taxo where
    type Label Taxo = ()

    relabel _ = id

    rootJoin tts@(Taxo h _ :| _) = Taxo (h+1) (MultiSet.fromList (NonEmpty.toList tts))

    liftRootJoin (t :| ts) = liftFoldr addDescendant emptyChain (t:ts)
      where
        emptyChain = fmap (\(Taxo h _) -> Taxo (h+1) MultiSet.empty) t


newtype Taxo1 a = Taxo1 Taxo
  deriving (Eq, Ord)

instance Show (Taxo1 a) where
    show (Taxo1 t) = show t

instance Ord a => TaxoLike (Taxo1 a) where
    type Label (Taxo1 a) = a
    relabel _ = id
    rootJoin = coerce (rootJoin @Taxo)
    liftRootJoin = coerce (liftRootJoin @Taxo)

liftTaxo1 :: (Int -> Height -> Prob Taxo) -> Int -> Height -> Prob (Taxo1 a)
liftTaxo1 = coerce

unliftTaxo1 :: (Int -> Height -> Prob (Taxo1 a)) -> Int -> Height -> Prob Taxo
unliftTaxo1 = coerce

level :: Depth -> Traversal' Taxo Taxo
level 0 f tree                 = f tree
level n f (Taxo h descendants) = Taxo h <$> (traverseMultiSet . level (n-1)) f descendants

chain :: Height -> Taxo
chain 0 = Taxo 0 MultiSet.empty
chain h = Taxo h (MultiSet.singleton (chain (h-1)))

addChain :: Taxo -> Taxo
addChain (Taxo h descendants)
  | MultiSet.null descendants = error "cannot add chain to leaf"
  | otherwise                 = Taxo h (MultiSet.insert (chain (h-1)) descendants)

addRandomChainUniform :: (ProbMonad m, Constr m Depth, Constr m Taxo) => m Depth -> Taxo -> m Taxo
addRandomChainUniform pdepth tree = do
    depth <- pdepth
    let depthNodes = lengthOf (level depth) tree
    nodeIdx <- uniformlySorted [0..depthNodes-1]
    return (tree & indexedLevel depth . index nodeIdx %~ addChain)
  where
    indexedLevel :: Depth -> IndexedTraversal' Int Taxo Taxo
    indexedLevel depth = conjoined (level depth) (indexing (level depth))

addRandomChainWeighted :: (ProbMonad m, Constr m Depth, Constr m Taxo) => m Depth -> Taxo -> m Taxo
addRandomChainWeighted pdepth taxo  = do
    depth <- pdepth
    navigateAndInsert depth taxo
  where
    navigateAndInsert 0     taxo                 = return (addChain taxo)
    navigateAndInsert depth (Taxo h descendants) = do
      let ndesc = MultiSet.size descendants
      i <- uniformlySorted [0..ndesc-1]

      let descList = MultiSet.toAscList descendants
      modifiedDescendant <- navigateAndInsert (depth-1) (descList !! i)

      let descendants' = MultiSet.fromList (descList & ix i .~ modifiedDescendant)
      return (Taxo h descendants')

addingLeavesUniform :: (ProbMonad m, Constr m Depth, Constr m Taxo) => Int -> Height -> m Depth -> m Taxo
addingLeavesUniform width height pdepth =
    case width of
      0 -> return (Taxo 0 MultiSet.empty)
      1 -> return start
      _ -> iterate (>>= addRandomChainUniform pdepth) (return start) !! (width-2)
             |>>=| addRandomChainUniform pdepth
  where
    start = chain height

addingLeavesWeighted :: (ProbMonad m, Constr m Depth, Constr m Taxo) => Int -> Height -> m Depth -> m Taxo
addingLeavesWeighted width height pdepth =
    case width of
      0 -> return (Taxo 0 MultiSet.empty)
      1 -> return start
      _ -> iterate (>>= addRandomChainWeighted pdepth) (return start) !! (width-2)
             |>>=| addRandomChainWeighted pdepth
  where
    start = chain height

addingLeavesProbUniform :: Int -> Prob Depth -> Prob Taxo
addingLeavesProbUniform width pdepth =
    addingLeavesUniform width height pdepth
  where
    height = maximum (eventValues pdepth) + 1

addingLeavesProbWeighted :: Int -> Prob Depth -> Prob Taxo
addingLeavesProbWeighted width pdepth =
    addingLeavesWeighted width height pdepth
  where
    height = maximum (eventValues pdepth) + 1

-- coalescentAssignments 1 3 (Taxo 0 [], Taxo 0 [], Taxo 0 [])
--   bottomAssignment = [[1,2],[0]]
--   coalescentAssignments 2 2 [Taxo 1 [Taxo 0 [], Taxo 0 []], Taxo 1 [Taxo 0 []]]
--     bottomAssignment = [[0,1]]
--     coalescentAssignments 3 1 [Taxo 2 [Taxo 1 [Taxo 0 [], Taxo 0 []], Taxo 1 [Taxo 0 []]]]
--       coalescentAssignments [Taxo 3 [Taxo 2 [Taxo 1 [Taxo 0 [], Taxo 0 []], Taxo 1 [Taxo 0 []]]]]

-- coalescentAssignments :: Height -> Int -> [Taxo] -> Prob Taxo
-- coalescentAssignments height 1     subLeaves = return (Taxo height (MultiSet.fromList subLeaves))
-- coalescentAssignments height depth subLeaves = do
--     let width = length subLeaves
--     bottomAssignment <- randomAssignmentFibres width [0..width-1]
--
--     coalescentAssignments (height+1) (depth-1) $
--         map (Taxo height . MultiSet.fromList . map (subLeaves!!)) bottomAssignment
--
-- coalescent :: Int -> Int -> Prob Taxo
-- coalescent width height = coalescentAssignments 1 height (replicate width (Taxo 0 MultiSet.empty))

coalescentForest :: Int -> Height -> Prob [Maybe Taxo]
coalescentForest = memo2 $ \w h ->
    case h of
      1 -> return [Just (chain 0) | i <- [0..w-1]]
      _ -> do
        prev <- coalescentForest w (h-1)
        parts <- randomAssignmentFibres w [0..w-1]
        let trees = map (mkTree (h-1) prev) parts
        return trees
  where
    mkTree :: Height -> [Maybe Taxo] -> [Int] -> Maybe Taxo
    mkTree h prev part =
        fmap rootJoin $ NonEmpty.nonEmpty [t | i <- part, Just t <- [prev!!i]]

coalescent :: Int -> Height -> Prob Taxo
coalescent w h = fmap joinForest (coalescentForest w h)
  where
    joinForest forest =
        case fmap rootJoin $ NonEmpty.nonEmpty [t | Just t <- forest] of
            Just t  -> t
            Nothing -> undefined

coalescentForestFixed :: Int -> Int -> Height -> Prob [Maybe Taxo]
coalescentForestFixed = memo2 $ \gridW w h ->
    case h of
      1 -> return $ [Just (chain 0) | i <- [0..w-1]] ++ replicate (gridW - w) Nothing
      _ -> do
        prev <- coalescentForestFixed gridW w (h-1)
        parts <- randomAssignmentFibres gridW [0..gridW-1]
        let trees = map (mkTree (h-1) prev) parts
        return trees
  where
    mkTree :: Height -> [Maybe Taxo] -> [Int] -> Maybe Taxo
    mkTree h prev part =
        fmap rootJoin $ NonEmpty.nonEmpty [t | i <- part, Just t <- [prev!!i]]

coalescentFixed :: Int -> Int -> Height -> Prob Taxo
coalescentFixed gridW w h = fmap joinForest (coalescentForestFixed gridW w h)
  where
    joinForest forest =
        case fmap rootJoin $ NonEmpty.nonEmpty [t | Just t <- forest] of
            Just t  -> t
            Nothing -> undefined

coalescentForestMonotone :: Int -> Height -> Prob [Taxo]
coalescentForestMonotone = memo2 $ \w h ->
    case h of
      1 -> return (replicate w (chain 0))
      _ -> do
        prev <- coalescentForestMonotone w (h-1)
        parts <- randomPartitionMonotone [0..length prev-1]
        return [Taxo (h-1) (MultiSet.fromList [prev !! i | i <- part]) | part <- parts]

coalescentMonotone :: Int -> Height -> Prob Taxo
coalescentMonotone w h =
    fmap (Taxo h . MultiSet.fromList) (coalescentForestMonotone w h)


genRandomProbs :: (ProbMonad m, Constr m Depth) => Height -> IO (m Depth)
genRandomProbs height = do
    let maxWeight = 1000 :: Int
        newWeight = R.rvar (R.Uniform 0 maxWeight)
    weights <- forM [0..height-2] $ \_ -> R.sample newWeight

    return $ fromEventsSorted $ weightedEvents (zip [0..] weights)

estimateProbs :: Taxo -> Prob Depth
estimateProbs taxo@(Taxo height _) =
    let insertionsPerLevel = [foldrOf (level i) countingInsertions 0 taxo | i <- [0..height-2]]
    in  fromEventsSorted (weightedEvents (zip [0..] insertionsPerLevel))
  where
    countingInsertions (Taxo _ children) acc = MultiSet.size children - 1 + acc


data AnnTaxo a = AnnTaxo { annTaxoHeight :: !Height, annTaxoChildren :: ![AnnTaxo a], annTaxoAnn :: !a }
  deriving (Eq, Ord)

annotateNumLeaves :: Taxo -> AnnTaxo Int
annotateNumLeaves (Taxo h desc)
  | MultiSet.null desc = AnnTaxo 0 [] 1
  | otherwise          =
      let desc' = map annotateNumLeaves (MultiSet.toList desc)
          nl    = sum (map annTaxoAnn desc')
      in  AnnTaxo h desc' nl

dropAnnotations :: AnnTaxo a -> Taxo
dropAnnotations (AnnTaxo h desc _) = Taxo h (MultiSet.fromList (map dropAnnotations desc))

removeLeaf :: Int -> AnnTaxo Int -> AnnTaxo Int
removeLeaf (!i) (AnnTaxo h []     _ ) = error "already at leaf, cannot remove"
removeLeaf (!i) (AnnTaxo h (d:ds) nl) =
    case d of
      AnnTaxo _ _ dnl
        | dnl <= i ->
            let AnnTaxo _ ds' _ = removeLeaf (i-dnl) (AnnTaxo h ds (nl-dnl))
            in  AnnTaxo h (d:ds') (nl-1)
        | dnl == 1  -> assert (i == 0) (AnnTaxo h ds (nl-1))
        | otherwise -> AnnTaxo h (removeLeaf i d : ds) (nl-1)

randomlyDeleteLeaf :: (ProbMonad m, Constr m Int, Constr m Taxo) => Taxo -> m Taxo
randomlyDeleteLeaf taxo = do
    let ann@(AnnTaxo _ _ nl) = annotateNumLeaves taxo
    i <- uniformlySorted [0..nl-1]
    return (dropAnnotations (removeLeaf i ann))

partitionModelUnif :: Int -> Int -> Prob Taxo
partitionModelUnif = memo2 t
  where
    t :: Int -> Int -> Prob Taxo
    t w 1 = return $ Taxo 1 (MultiSet.fromAscOccurList [(Taxo 0 MultiSet.empty, w)])
    t w h = do
        parts <- randomPartitionUnif w
        let psubtrees = map (\part -> partitionModelUnif part (h-1)) parts
        fmap (rootJoin . NonEmpty.fromList) (sequence psubtrees)

partitionModelFixed :: Int -> Int -> Prob Taxo
partitionModelFixed = memo2 t
  where
    t :: Int -> Int -> Prob Taxo
    t w 1 = return $ Taxo 1 (MultiSet.fromAscOccurList [(Taxo 0 MultiSet.empty, w)])
    t w h = do
        parts <- randomPartitionFixing w
        let psubtrees = map (\part -> partitionModelFixed part (h-1)) parts
        liftRootJoin (NonEmpty.fromList psubtrees)
