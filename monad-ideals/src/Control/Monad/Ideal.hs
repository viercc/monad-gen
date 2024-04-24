-----------------------------------------------------------------------------
-- |
-- Module      :  Control.Monad.Ideal
-- Copyright   :  (C) 2008 Edward Kmett, (C) 2024 Koji Miyazato
-- License     :  BSD-style (see the file LICENSE)
--
-- Maintainer  :  Koji Miyazato <viercc@gmail.com>
-- Stability   :  experimental
-- Portability :  portable
module Control.Monad.Ideal
  ( -- * Ideal Monads
    MonadIdeal (..),
    Ideal,
    ideal,
    destroyIdeal,

    -- * Mutual recursion for (co)ideal (co)monad (co)products
    Mutual (..), Mutual'(..),

    -- * Ideal Monad Coproduct
    (:+),
    inject1,
    inject2,
    (||||),
  )
where

import Control.Functor.Internal.Ideal
