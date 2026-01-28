{-# LANGUAGE RankNTypes #-}
module Util where

import qualified System.IO as IO
import qualified System.Console.ANSI as Console

import Data.Coerce
import System.Exit (exitFailure)
import qualified Data.Time as Time
import qualified Data.Time.Format.ISO8601 as Time
import System.Console.ANSI.Types

dieWithErrors :: [String] -> IO a
dieWithErrors errs = mapM_ (IO.hPutStrLn IO.stderr) errs >> exitFailure

coerceMap :: Coercible (f a) (f b) => (a -> b) -> f a -> f b
coerceMap _ = coerce

type Logger = forall a. ((String -> IO ()) -> IO a) -> IO a

discard :: Logger
discard body = body (const (pure ()))

timed :: Logger -> Logger
timed logger body =
  logger $ \log' -> do
    body $ \line -> do
      now <- Time.getZonedTime
      log' $ "[" ++ Time.iso8601Show now ++ "]" ++ line

loggedTo :: FilePath -> Logger -> Logger
loggedTo filePath logger body =
  IO.withFile filePath IO.AppendMode $ \h ->
    logger $ \log' ->
      body $ \line -> do
        log' line
        IO.hPutStrLn h line

statusLine :: Logger -> Logger
statusLine logger body =
  logger $ \log' -> do
    a <- body $ \line -> do
      log' line
      Console.clearLine
      Console.setSGR [SetColor Foreground Vivid Green]
      IO.putStrLn line
      Console.setSGR [Reset]
      Console.cursorUpLine 1
    Console.cursorDownLine 1
    pure a
