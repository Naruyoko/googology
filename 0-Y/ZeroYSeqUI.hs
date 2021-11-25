import System.Environment ( getArgs )
import ZeroYSeq
    ( (!),
      joinString,
      parseSequence,
      stringifySequence,
      calcMountain,
      stringifyMountain,
      expand,
      calcSteps )

processArgs :: [String] -> IO ()
processArgs args = case (head args, length args) of
  ("calcMountain", 2) ->
    let seq = parseSequence $ args ! 1 in
    putStrLn $ stringifyMountain $ calcMountain seq
  ("expand", 3) ->
    let seq = parseSequence $ args ! 1
        ns = (parseSequence $ args ! 2) in
    putStrLn $ stringifySequence $ foldl expand seq ns
  ("calc", 3) ->
    let seq = parseSequence $ args ! 1
        n = (read $ args ! 2 :: Integer) in
    putStrLn $ (++) "  " $ go $ calcSteps (+1) seq n
    where go ((seq,n):xs) = "(" ++ stringifySequence seq ++ ")" ++ (if null xs then "" else "\n[" ++ show n ++ "]> " ++ go xs)
  ("calc", 4) ->
    let seq = parseSequence $ args ! 1
        n = (read $ args ! 2 :: Integer)
        linen = (read $ args ! 3 :: Integer) in
    putStrLn $ (++) "  " $ go linen $ calcSteps (+1) seq n
    where go linen ((seq,n):xs) = "(" ++ stringifySequence seq ++ ")" ++ (if null xs || linen == 0 then "" else "\n[" ++ show n ++ "]> " ++ go (linen-1) xs)
  ("calcid", 3) ->
    let seq = parseSequence $ args ! 1
        n = (read $ args ! 2 :: Integer) in
    putStrLn $ (++) (replicate (length $ "[" ++ show n ++ "]> ") ' ') $ go $ calcSteps id seq n
    where go ((seq,n):xs) = "(" ++ stringifySequence seq ++ ")" ++ (if null xs then "" else "\n[" ++ show n ++ "]> " ++ go xs)
  ("calcid", 4) ->
    let seq = parseSequence $ args ! 1
        n = (read $ args ! 2 :: Integer)
        linen = (read $ args ! 3 :: Integer) in
    putStrLn $ (++) (replicate (length $ "[" ++ show n ++ "]> ") ' ') $ go linen $ calcSteps id seq n
    where go linen ((seq,n):xs) = "(" ++ stringifySequence seq ++ ")" ++ (if null xs || linen == 0 then "" else "\n[" ++ show n ++ "]> " ++ go (linen-1) xs)
  ("help", 1) ->
    putStrLn $ unlines [ "Usage:",
                         "  calcMountain <sequence> : Displays the mountain built from <sequence>",
                         "  expand <sequence> <n> : Expands <sequence> by [<n>]",
                         "  calc <sequence> <n> : Calculates <sequence>[<n>], showing each steps of expansion. Continues until termination, i.e. the sequence becomes empty",
                         "  calc <sequence> <n> <linen> : Calculates <sequence>[<n>] for <linen> steps, showing each steps of expansion. It may also end when it terminates, i.e. the sequence becomes empty",
                         "  calcid <sequence> <n> : Same as calc <sequence> <n>, but <n> is constant",
                         "  calcid <sequence> <n> <linen> : Same as calc <sequence> <n> <linen>, but <n> is constant",
                         "  help : Displays this text",
                         "  quit : Quits the program" ]
  _ -> putStrLn $ "Unknown command " ++ head args ++ " with " ++ show (length args-1) ++ " argument(s), use help command for a list of commands"

loopAndTakeInputs :: IO ()
loopAndTakeInputs = do
  line <- getLine
  if null line
    then loopAndTakeInputs
  else if line == "quit"
    then putStrLn ""
    else do
      processArgs $ words line
      loopAndTakeInputs

main :: IO ()
main = do
  args <- getArgs
  if null args
    then do
      putStrLn "I'm listening..."
      loopAndTakeInputs
    else processArgs args