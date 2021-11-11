import System.Environment ( getArgs )
import ZeroYSeq
    ( (!),
      parseSequence,
      stringifySequence,
      calcMountain,
      stringifyMountain,
      expand,
      calcDispStep )

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
    putStrLn $ (++) "  " $ calcDispStep (+1) seq n
  ("calcid", 3) ->
    let seq = parseSequence $ args ! 1
        n = (read $ args ! 2 :: Integer) in
    putStrLn $ (++) (replicate (length $ "[" ++ show n ++ "]> ") ' ') $ calcDispStep id seq n
  _ -> putStrLn $ "Unknown command " ++ head args ++ " with " ++ show (length args-1) ++ " argument(s)"

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