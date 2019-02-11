{-# OPTIONS_GHC -ddump-simpl -dsuppress-all #-}

module Test where

import Control.Monad.Freer
import Control.Monad.Freer.State


oneGet :: Int -> (Int, Int)
oneGet n = run (runState n get)

main :: IO ()
main = print $ oneGet 15

