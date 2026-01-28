{-# LANGUAGE RankNTypes #-}
module Util where

import qualified System.IO as IO
import qualified System.Console.ANSI as Console

import Data.Coerce
import System.Exit (exitFailure)
import qualified Data.Time as Time
import qualified Data.Time.Format.ISO8601 as Time

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

statusLine :: String -> Logger -> Logger
statusLine label logger body =
  logger $ \log' ->
    body $ \line -> do
      log' line
      IO.putStrLn label
      IO.putStrLn line
      Console.cursorUpLine 2
      Console.clearFromCursorToScreenEnd
