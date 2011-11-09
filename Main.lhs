A main module for gluing the parsing together.

> module Main where
> import Prelude hiding (div, id, mod, repeat, succ, pred, sum, product)
> import System (getArgs)
> import SKI
> import Parsing
> import ML

> main = do
>   args <- getArgs
>   contents <- readFile (head args)
>   putStrLn $ show (parseResult (parse ML.prog contents))
>     where
>       parseResult [] = "No valid parse!"
>       parseResult [(a,s)] = show $ (execute . compile) a
