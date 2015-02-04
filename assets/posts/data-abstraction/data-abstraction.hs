#!/usr/bin/env runghc

{-# LANGUAGE RankNTypes,ExistentialQuantification,ScopedTypeVariables #-}

import Prelude hiding (id,min,Ord,(<=))
import qualified Prelude as P

class Ord a where
  (<=) :: a -> a -> Bool

instance Ord Int where
  (<=) = (P.<=)

min :: forall a. Ord a => a -> a -> a
min x y = if x <= y then x else y

main :: IO ()
main = do
	print $ min (9::Int) (3::Int)
