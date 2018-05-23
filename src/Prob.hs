{-# language BangPatterns #-}
{-# language ConstraintKinds #-}
{-# language DefaultSignatures #-}
{-# language FlexibleContexts #-}
{-# language FlexibleInstances #-}
{-# language GeneralizedNewtypeDeriving #-}
{-# language RankNTypes #-}
{-# language RebindableSyntax #-}
{-# language TypeFamilies #-}
module Prob where

import Prelude hiding (Functor(..), Applicative(..), Monad(..), sequence, (=<<), mapM, mapM_)
import qualified Prelude

import GHC.Exts (Constraint)

import Control.DeepSeq (NFData(..), force)
import Control.Parallel.Strategies (withStrategy, rpar, rseq, parList, parListChunk)
import Control.Monad.State (State)

import Data.List (groupBy, sort, sortBy)
import Data.List.NonEmpty (NonEmpty(..))
import qualified Data.Random                          as R
import qualified Data.Random.Distribution.Categorical as R

import Numeric.SpecFunctions (choose)


type QQ = Rational

data Event a = Event !a !QQ deriving (Eq, Ord)

eventToPair :: Event a -> (a, QQ)
eventToPair (Event a p) = (a, p)
{-# inline eventToPair #-}

mapEvent :: (a -> b) -> Event a -> Event b
mapEvent f (Event a p) = Event (f a) p
{-# inline mapEvent #-}

instance NFData a => NFData (Event a) where
    rnf (Event a _) = rnf a

instance Show a => Show (Event a) where
    show (Event a p) = show a ++ ": " ++ show p -- (realToFrac p :: Float)

newtype Prob a = Prob { density :: [Event a] } deriving (Eq, Ord, Show, NFData)

events :: Prob a -> [Event a]
events (Prob es) = es

eventValues :: Prob a -> [a]
eventValues prob = [a | Event a _ <- events prob]

eventProbs :: Prob a -> [QQ]
eventProbs prob = [p | Event _ p <- events prob]

class NoConstr a
instance NoConstr a

class ConstrMonad m where
    type Constr m :: * -> Constraint
    type Constr m = NoConstr

    fmap :: Constr m b => (a -> b) -> m a -> m b
    fmap f ma = do
        a <- ma
        return (f a)

    return :: Constr m a => a -> m a
    (>>=)  :: Constr m b => m a -> (a -> m b) -> m b

    (|>>=|) :: (Constr m a, Constr m b) => m a -> (a -> m b) -> m b
    (|>>=|) = (>>=)

    default return :: Prelude.Monad m => a -> m a
    return = Prelude.return
    default (>>=) :: Prelude.Monad m => m a -> (a -> m b) -> m b
    ma >>= f = ma Prelude.>>= f

infixl 1 >>=


liftA2 :: (ConstrMonad m, Constr m a, Constr m b, Constr m d) => (a -> b -> d) -> m a -> m b -> m d
liftA2 f ma mb = do
    a <- ma
    b <- mb
    return (f a b)
{-# inline liftA2 #-}

liftA3 :: (ConstrMonad m, Constr m a, Constr m b, Constr m d, Constr m e) => (a -> b -> d -> e) -> m a -> m b -> m d -> m e
liftA3 f ma mb md = do
    a <- ma
    b <- mb
    d <- md
    return (f a b d)
{-# inlinable liftA3 #-}

(=<<)  :: (ConstrMonad m, Constr m a, Constr m b) => (a -> m b) -> m a -> m b
f =<< ma = ma >>= f
infixr 1 =<<
{-# inline (=<<) #-}


instance ConstrMonad Maybe
instance ConstrMonad IO
instance ConstrMonad (State s)

instance Prelude.Monad m => ConstrMonad (R.RVarT m)
instance Prelude.Monad m => ProbMonad (R.RVarT m) where
    fromEventsSorted evts = R.categoricalT [(realToFrac p :: Double, a) | Event a p <- evts]

weightedEvents :: Real b => [(a, b)] -> [Event a]
weightedEvents es = [Event a (realToFrac w / s) | (a,w) <- es]
  where
    s = realToFrac $ sum [w | (_,w) <- es]

rnfList :: [a] -> ()
rnfList []     = ()
rnfList (a:as) = a `seq` rnfList as

forceList :: [a] -> [a]
forceList as = rnfList as `seq` as

fmapProb :: Ord b => (a -> b) -> Prob a -> Prob b
fmapProb f (Prob [Event a p]) = Prob [Event (f a) p]
fmapProb f (Prob evts)        =
    Prob $ forceList $ group1 $ sortBy (\(Event b _) (Event b' _) -> compare b b') [Event (f a) p | Event a p <- evts]
  where
    group1 :: Ord a => [Event a] -> [Event a]
    group1 []     = []
    group1 (e:es) = group e es

    group :: Ord a => Event a -> [Event a] -> [Event a]
    group e@(Event a p) ees =
      case ees of
        [] -> [e]
        e'@(Event a' p') : es
          | a == a'   -> group (Event a (p + p')) es
          | otherwise -> e : group e' es

{-# inlinable fmapProb #-}

bindProbWithStrat :: Ord b => (forall c. [c] -> [c]) -> Prob a -> (a -> Prob b) -> Prob b
bindProbWithStrat evalList (Prob [Event a _]) f = Prob $ evalList $ events (f a)
bindProbWithStrat evalList (Prob evts) f =
    Prob $ forceList $ group1 $ merge1 $ evalList $ totalProb [Event (f a) p | Event a p <- evts]
  where
    totalProb :: [Event (Prob a)] -> [[Event a]]
    totalProb ess = [[Event b (p*p') | Event b p' <- es] | Event (Prob es) p <- ess]

    merge1 :: Ord a => [[Event a]] -> [Event a]
    merge1 []       = []
    merge1 (es:ess) = merge es ess

    merge :: Ord a => [Event a] -> [[Event a]] -> [Event a]
    merge es []             = es
    merge es (es':[])       = merge2 es es'
    merge es (es':es'':ess) = merge2 (merge2 es es') (merge es'' ess)

    merge2 :: Ord a => [Event a] -> [Event a] -> [Event a]
    merge2 as         []         = as
    merge2 []         bs         = bs
    merge2 aas@(a:as) bbs@(b:bs)
      | a <= b    = a : merge2 as bbs
      | otherwise = b : merge2 aas bs

    group1 :: Ord a => [Event a] -> [Event a]
    group1 []     = []
    group1 (e:es) = group e es

    group :: Ord a => Event a -> [Event a] -> [Event a]
    group e@(Event a p) ees =
      case ees of
        [] -> [e]
        e'@(Event a' p') : es
          | a == a'   -> group (Event a (p + p')) es
          | otherwise -> e : group e' es

{-# inlinable bindProbWithStrat #-}

instance ConstrMonad Prob where
    type Constr Prob = Ord

    fmap = fmapProb
    {-# inline fmap #-}

    return a = Prob [Event a 1]
    {-# inline return #-}

    (>>=) = bindProbWithStrat forceList
    {-# inline (>>=) #-}

    -- (|>>=|) :: (Ord a, Ord b) => Prob a -> (a -> Prob b) -> Prob b
    (|>>=|) = bindProbWithStrat (withStrategy $ parList rseq)
    {-# inline (|>>=|) #-}


(|=<<|) :: (Ord a, Ord b) => (a -> Prob b) -> Prob a -> Prob b
f |=<<| ma = ma |>>=| f
{-# inline (|=<<|) #-}

ifThenElse :: Bool -> a -> a -> a
ifThenElse True  t _ = t
ifThenElse False _ f = f
{-# inline ifThenElse #-}

fail :: a
fail = error "fail called"

(>>) :: (ConstrMonad m, Constr m (), Constr m b) => m a -> m b -> m b
ma >> mb = fmap (\_ -> ()) ma >>= \() -> mb
infixl 1 >>
{-# inline (>>) #-}

(<<) :: (ConstrMonad m, Constr m (), Constr m b) => m b -> m a -> m b
mb << ma = ma >> mb
infixr 1 <<
{-# inline (<<) #-}

sequence :: (ConstrMonad m, Constr m a, Constr m [a]) => [m a] -> m [a]
sequence []       = return []
sequence (ma:mas) = liftA2 (:) ma (sequence mas)
{-# inlinable sequence #-}

mapM :: (ConstrMonad m, Constr m b, Constr m [b]) => (a -> m b) -> [a] -> m [b]
mapM f []     = return []
mapM f (a:as) = liftA2 (:) (f a) (mapM f as)
{-# inlinable mapM #-}

mapM_ :: (ConstrMonad m, Constr m ()) => (a -> m ()) -> [a] -> m ()
mapM_ f []     = return ()
mapM_ f (a:as) = f a >> mapM_ f as
{-# inlinable mapM_ #-}

forM :: (ConstrMonad m, Constr m b, Constr m [b]) => [a] -> (a -> m b) -> m [b]
forM as f = mapM f as
{-# inline forM #-}

forM_ :: (ConstrMonad m, Constr m ()) => [a] -> (a -> m ()) -> m ()
forM_ as f = mapM_ f as
{-# inline forM_ #-}

sequence1 :: (ConstrMonad m, Constr m a, Constr m [a], Constr m (NonEmpty a)) => NonEmpty (m a) -> m (NonEmpty a)
sequence1 (ma:|mas) = liftA2 (:|) ma (sequence mas)
{-# inline sequence1 #-}

mapM1 :: (ConstrMonad m, Constr m b, Constr m [b], Constr m (NonEmpty b)) => (a -> m b) -> NonEmpty a -> m (NonEmpty b)
mapM1 f (a:|as) = liftA2 (:|) (f a) (mapM f as)
{-# inline mapM1 #-}

forM1 :: (ConstrMonad m, Constr m b, Constr m [b], Constr m (NonEmpty b)) => NonEmpty a -> (a -> m b) -> m (NonEmpty b)
forM1 as f = mapM1 f as
{-# inline forM1 #-}


liftFoldl' :: (ConstrMonad m, Constr m a, Constr m b) => (b -> a -> b) -> m b -> [m a] -> m b
liftFoldl' _ !z []     = z
liftFoldl' f !z (p:ps) = liftFoldl' f (liftA2 f z p) ps

liftFoldr :: (ConstrMonad m, Constr m a, Constr m b) => (a -> b -> b) -> m b -> [m a] -> m b
liftFoldr f z = foldr (liftA2 f) z

liftFold :: (ConstrMonad m, Constr m a, Monoid a) => [m a] -> m a
liftFold = liftFoldl' mappend (return mempty)

liftSum :: (ConstrMonad m, Constr m a, Num a) => [m a] -> m a
liftSum = liftFoldl' (+) (return 0)


class ConstrMonad m => ProbMonad m where
    fromEventsSorted :: Constr m a => [Event a] -> m a

instance ProbMonad Prob where
    fromEventsSorted = Prob

uniformly :: (ProbMonad m, Constr m a, Ord a) => [a] -> m a
uniformly = uniformlySorted . sort

uniformlySorted :: (ProbMonad m, Constr m a) => [a] -> m a
uniformlySorted as = fromEventsSorted [Event a (1/n) | a <- as]
  where
    n = fromIntegral (length as)

probTrue :: Prob Bool -> QQ
probTrue prob =
    case events prob of
        [Event False _, Event True p] -> p
        [Event True p]                -> p
        [Event False q]               -> 1 - q
        []                            -> error "empty Prob!"
        _                             -> error "unnormalized Prob!"

probFalse :: Prob Bool -> QQ
probFalse prob = 1 - probTrue prob

eventProb :: Eq a => a -> Prob a -> QQ
eventProb e prob =
    case [p | Event a p <- events prob, a == e] of
      []  -> 0
      [p] -> p
      _   -> error "eventProb: prob is not normalized"

probOf :: (a -> Bool) -> Prob a -> QQ
probOf test prob = sum [p | Event a p <- events prob, test a]

given :: (a -> Bool) -> Prob a -> Prob a
given hyp prob =
    Prob [Event a (p / probHyp) | Event a p <- events prob, hyp a]
  where
    probHyp = probOf hyp prob

bernoulli :: QQ -> Prob Bool
bernoulli p = Prob [Event False (1-p), Event True p]

binomial :: Int -> QQ -> Prob Int
binomial 0 _ = return 0
binomial n p =
    case p of
      0 -> force $ return 0
      1 -> force $ return n
      _ -> force $ Prob [Event k (binomialProb n p k) | k <- [0..n]]

binomialProb :: Int -> QQ -> Int -> QQ
binomialProb n p k
  | k < 0 || k > n = 0
  | n == 0         = 1
  | otherwise      = realToFrac (choose n k) * p^k * (1-p)^fromIntegral (n-k)

distribution :: Ord a => Prob a -> [Event a]
distribution (Prob evts) = scanl1 sumEvents evts
  where
    sumEvents (Event _ p) (Event a' p') = Event a' (p + p')

revDistribution :: Ord a => Prob a -> [Event a]
revDistribution (Prob evts) = scanr1 sumEvents evts
  where
    sumEvents (Event a p) (Event _ p') = Event a (p + p')

summary :: Prob QQ -> IO ()
summary p =
  let mu    = "µ=" ++ show (realToFrac (mean p) :: Double)
      sigma = "σ=" ++ show (sqrt $ realToFrac (variance p) :: Double)
  in
      putStrLn $ mu ++ ", " ++ sigma

summaryInt :: Prob Int -> IO ()
summaryInt = summary . fmap fromIntegral

mean :: Prob QQ -> QQ
mean prob = sum [k * p | Event k p <- events prob]

variance :: Prob QQ -> QQ
variance prob = sum [k^2 * p | Event k p <- events prob] - mean prob^2

maxEvent :: Ord a => Prob a -> a
maxEvent (Prob es) = maximum [a | Event a _ <- es]
