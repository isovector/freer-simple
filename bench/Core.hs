{-# OPTIONS_GHC -ddump-simpl-stats -dsuppress-all -fno-warn-unused-top-binds #-}

module Main (main) where

import Control.Monad (replicateM_)

import qualified Control.Monad.Except as MTL
import qualified Control.Monad.State as MTL

import Criterion (bench, bgroup, whnf)
import Criterion.Main (defaultMain)

import Control.Monad.Freer (Member, Eff, run, send)
import Control.Monad.Freer.Internal (Eff(..), decomp, qApp, tsingleton)
import Control.Monad.Freer.Error (runError, throwError)
import Control.Monad.Freer.State (get, put, runState)

--------------------------------------------------------------------------------
                        -- State Benchmarks --
--------------------------------------------------------------------------------

oneGet :: Int -> (Int, Int)
oneGet n = run (runState n get)

oneGetMTL :: Int -> (Int, Int)
oneGetMTL = MTL.runState MTL.get

countDown :: Int -> (Int, Int)
countDown start = run (runState start go)
  where go = get >>= (\n -> if n <= 0 then pure n else put (n-1) >> go)

countDownMTL :: Int -> (Int, Int)
countDownMTL = MTL.runState go
  where go = MTL.get >>= (\n -> if n <= 0 then pure n else MTL.put (n-1) >> go)

--------------------------------------------------------------------------------
                       -- Exception + State --
--------------------------------------------------------------------------------
countDownExc :: Int -> Either String (Int,Int)
countDownExc start = run $ runError (runState start go)
  where go = get >>= (\n -> if n <= (0 :: Int) then throwError "wat" else put (n-1) >> go)

countDownExcMTL :: Int -> Either String (Int,Int)
countDownExcMTL = MTL.runStateT go
  where go = MTL.get >>= (\n -> if n <= (0 :: Int) then MTL.throwError "wat" else MTL.put (n-1) >> go)

main :: IO ()
main =
  defaultMain [
    -- bgroup "State" [
    --     bench "freer.get"          $ whnf oneGet 0
    --   -- , bench "mtl.get"            $ whnf oneGetMTL 0
    -- ],
    bgroup "Countdown Bench" [
        bench "freer.State"    $ whnf countDown 10000
      -- , bench "mtl.State"      $ whnf countDownMTL 10000
    ],
    bgroup "Countdown+Except Bench" [
        bench "freer.ExcState"  $ whnf countDownExc 10000
      -- , bench "mtl.ExceptState" $ whnf countDownExcMTL 10000
    ]
  ]
