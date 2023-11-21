module Util where

import qualified System.IO as IO
import qualified System.Console.ANSI as Console

import Data.IORef

import Data.Coerce
import Control.Monad (when)

coerceMap :: Coercible (f a) (f b) => (a -> b) -> f a -> f b
coerceMap _ = coerce

writeFile' :: FilePath -> ((String -> IO ()) -> IO ()) -> IO ()
writeFile' filePath body =
  IO.withFile filePath IO.WriteMode $ \h ->
    do putStrLn $ "Writing " ++ show filePath
       putStrLn "Line [0]"
       counter <- newIORef (1 :: Int)
       body $ \l ->
         do IO.hPutStrLn h l
            Console.cursorUp 1
            i <- readIORef counter
            when ((i + 1) `mod` 100 == 0) $ putStrLn $ "Line [" ++ show (i + 1) ++ "]"
            writeIORef counter (i+1)


writeFile'debug :: FilePath -> ((String -> IO ()) -> IO ()) -> IO ()
writeFile'debug filePath body =
  IO.withFile filePath IO.WriteMode $ \h ->
    do putStrLn $ "Writing " ++ show filePath
       putStrLn "Line [0]"
       counter <- newIORef (1 :: Int)
       body $ \l ->
         do IO.hPutStrLn h l
            i <- readIORef counter
            putStrLn $ "Line [" ++ show (i + 1) ++ "]"
            writeIORef counter (i+1)

