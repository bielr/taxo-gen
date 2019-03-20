{-# language BangPatterns #-}
{-# language LambdaCase #-}
{-# language RebindableSyntax #-}
{-# language TypeApplications #-}
module Main where

import Prelude hiding (Functor(..), Applicative(..), Monad(..), sequence, (=<<), mapM, mapM_)
import qualified Prelude
import Prob
import Util

import Data.List (intercalate, nub, permutations)
import qualified Data.List.NonEmpty as NonEmpty
import Data.Ratio (numerator, denominator)

import System.Environment
import System.Exit (die)

import qualified TaxoGen
import qualified TaxoGenLab
import qualified TaxoGenOrd


data GenArgs =
    GenModel    (Int -> Int -> Prob TaxoGen.Taxo)          Int Height
  | GenModelLab (Int -> Int -> Prob (TaxoGenLab.Taxo Int)) Int Height
  | GenModelOrd (Int -> Int -> Prob (TaxoGenOrd.Taxo Int)) Int Height

main = do
    progName <- getProgName
    args <- getArgs

    case args of
        "distrib":args' ->
            parseArgs args' >>= \case
                GenModel    model width height -> printProbTaxo $ model width height
                GenModelLab model width height -> printProbTaxo $ model width height
                GenModelOrd model width height -> printProbTaxo $ model width height

        "markovian":args' ->
            parseArgs args' >>= \case
                GenModel model width height -> do
                    let parts = map NonEmpty.fromList $ concatMap (nub . permutations) (intPartitions width)
                    mapM_ (putStrLn . showEqn) $ markovianEqns parts (TaxoGen.liftTaxo1 @Int model) width height
                    print (map NonEmpty.toList parts)
                GenModelLab model width height -> do
                    let parts = map NonEmpty.fromList $ concatMap (nub . permutations) (intPartitions width)
                    mapM_ (putStrLn . showEqn) $ markovianEqns parts model width height
                    print (map NonEmpty.toList parts)
                GenModelOrd model width height -> do
                    let parts = map NonEmpty.fromList $ concatMap (nub . permutations) (intPartitions width)
                    mapM_ (putStrLn . showEqn) $ markovianEqns parts model width height
                    print (map NonEmpty.toList parts)

        "markovian-sym":args' -> do
            parseArgs args' >>= \case
                GenModel model width height -> do
                    let parts = map NonEmpty.fromList $ intPartitions width
                    mapM_ (putStrLn . showEqn) $ markovianEqns parts (TaxoGen.liftTaxo1 @Int model) width height
                    print (map NonEmpty.toList parts)
                GenModelLab model width height -> do
                    let parts = map NonEmpty.fromList $ intPartitions width
                    mapM_ (putStrLn . showEqn) $ markovianEqns parts model width height
                    print (map NonEmpty.toList parts)
                GenModelOrd _ _ _ ->
                    die "markovian-sym not available for ordered models"

        cmd:_ -> do
            die $ "unknown command: " ++ cmd

  where
    parseArgs :: [String] -> IO GenArgs
    parseArgs ("remove-leaf":args') = do
        parseArgs args' >>= \case
            GenModel    model width height -> return $ GenModel    (\w h -> model w h >>= TaxoGen.randomlyDeleteLeaf)   width height
            GenModelLab model width height -> return $ GenModelLab (\w h -> fmap TaxoGenLab.deleteLastLeaf (model w h)) width height
            GenModelOrd model width height -> return $ GenModelOrd (\w h -> fmap TaxoGenOrd.deleteLastLeaf (model w h)) width height

    parseArgs ("unlabeled":args') = do
        parseArgs args' >>= \case
            GenModel    model width height -> return $ GenModel model                                           width height
            GenModelLab model width height -> return $ GenModel (\w h -> fmap TaxoGenLab.unlabeled (model w h)) width height

    parseArgs ("unordered":args') = do
        parseArgs args' >>= \case
            GenModel    model width height -> return $ GenModel    model                                           width height
            GenModelLab model width height -> return $ GenModelLab model                                           width height
            GenModelOrd model width height -> return $ GenModelLab (\w h -> fmap TaxoGenOrd.unordered (model w h)) width height

    -- UNLABELED

    parseArgs ["adding-leaves-level", s_width, s_height] = do
        let (width, height) = (read s_width, read s_height)
            model w h = TaxoGen.addingLeavesProbUniform w (uniformlySorted [0..h-1])
        return $ GenModel model width height

    parseArgs ["adding-leaves", s_width, s_height] = do
        let (width, height) = (read s_width, read s_height)
            model w h = TaxoGen.addingLeavesProbWeighted w (uniformlySorted [0..h-1])

        return $ GenModel model width height

    parseArgs ["coalescent", s_width, s_height] = do
        let (width, height) = (read s_width, read s_height)
        return $ GenModel TaxoGen.coalescent width height

    parseArgs ["coalescent-mon", s_width, s_height] = do
        let (width, height) = (read s_width, read s_height)
        return $ GenModel TaxoGen.coalescentMonotone width height

    parseArgs ["coalescent-fixed", s_gridW, s_width, s_height] = do
        let (gridW, width, height) = (read s_gridW, read s_width, read s_height)
        return $ GenModel (TaxoGen.coalescentFixed gridW) width height

    parseArgs ["partition", s_width, s_height] = do
        let (width, height) = (read s_width, read s_height)
        return $ GenModel TaxoGen.partitionModelUnif width height

    parseArgs ["partition-fixed", s_width, s_height] = do
        let (width, height) = (read s_width, read s_height)
        return $ GenModel TaxoGen.partitionModelFixed width height

    -- LABELED

    parseArgs ["adding-leaves-lab", s_width, s_height] = do
        let (width, height) = (read s_width, read s_height)
            model w h       = TaxoGenLab.addingLeavesProbWeighted w (uniformlySorted [0..h-1])
        return $ GenModelLab model width height

    parseArgs ["coalescent-lab", s_width, s_height] = do
        let (width, height) = (read s_width, read s_height)
        return $ GenModelLab TaxoGenLab.coalescent width height

    parseArgs ["coalescent-mon-lab", s_width, s_height] = do
        let (width, height) = (read s_width, read s_height)
        return $ GenModelLab TaxoGenLab.coalescentMonotone width height

    -- LABELED & ORDERED

    parseArgs ["coalescent-lab-ord", s_width, s_height] = do
        let (width, height) = (read s_width, read s_height)
        return $ GenModelOrd TaxoGenOrd.coalescent width height

    parseArgs ["coalescent-mon-lab-ord", s_width, s_height] = do
        let (width, height) = (read s_width, read s_height)
        return $ GenModelOrd TaxoGenOrd.coalescentMonotone width height

    -- UTILITIES

    parseArgs args = die $ "cannot parse arguments: " ++ unwords args

    showEqn :: (QQ, [(a, QQ)]) -> String
    showEqn (lhs, rhs) = showRational lhs ++ "\t" ++ intercalate "\t" (map (showRational . snd) rhs)
    --showEqn (lhs, rhs) = showRational lhs ++ " = " ++ intercalate " + " (map showSummand rhs)
    --showSummand (part, coeff) = showRational coeff ++ " * x_{" ++ intercalate "," (map show part) ++ "}"
    showRational r = show (numerator r) ++ "/" ++ show (denominator r)

    printProbTaxo dist =
        forM_ (events dist) $ \(Event a p) -> do
            let strTree = show a
                strProb = showRational p
            putStrLn (show strTree ++ "\t" ++ show strProb) -- quoted tsv
