{-# LANGUAGE TupleSections #-}

-- HexirpさんのBashicu.hsを参考にしました

module ZeroYSeq where
import System.Environment
import Data.List
import Data.Maybe
import Data.Bifunctor

(!) :: [a] -> Integer -> a
[] ! _ = undefined
(x:xs) ! 0 = x
(x:xs) ! n = xs ! (n-1)

infixl 9 !

ilength :: [a] -> Integer
ilength xs = genericLength xs :: Integer

itake :: Integer -> [a] -> [a]
itake = genericTake

idrop :: Integer -> [a] -> [a]
idrop = genericDrop

replaceAt :: [a] -> Int -> a -> [a]
replaceAt arr index new = take index arr ++ (new : drop (index+1) arr)

replaceAt2D :: [[a]] -> Int -> Int -> a -> [[a]]
replaceAt2D arr y x new = replaceAt arr y $ replaceAt (arr !! y) x new

ireplaceAt :: [a] -> Integer -> a -> [a]
ireplaceAt arr index new = itake index arr ++ (new : idrop (index+1) arr)

ireplaceAt2D :: [[a]] -> Integer -> Integer -> a -> [[a]]
ireplaceAt2D arr y x new = ireplaceAt arr y $ ireplaceAt (arr ! y) x new

type Sequence = [Integer]
data POffset = NoParent | HasParent Integer
type VPPair = (Integer,POffset)
type MountainRow = [Maybe VPPair]
type Mountain = [MountainRow]
type UnfilledVPPair = (Maybe Integer,POffset)
type UnfilledMountainRow = [Maybe UnfilledVPPair]
type UnfilledMountain = [UnfilledMountainRow]

split :: Char -> String -> [String]
split char "" = []
split char str =
  case elemIndex char str of
    Just index -> take index str : split char (drop (index+1) str)
    Nothing -> [str]

join :: Char -> [String] -> String
join char [] = ""
join char [str] = str
join char (str:strs) = str ++ singleton char ++ join char strs

parseSequence :: String -> Sequence
parseSequence input = map (\x -> read x :: Integer) $ split ',' input

stringifySequence :: Sequence -> String
stringifySequence seq = join ',' $ map show seq

isValid :: Sequence -> Bool
isValid (x:xs) = x==1 && all (>=1) xs

parent :: Maybe MountainRow -> MountainRow -> Integer -> POffset
parent last row index = if isNothing $ row ! index then NoParent else go index
  where go p
          | isNothing $ row ! p = NoParent
          | fst (fromJust $ row ! p) < fst (fromJust $ row ! index) = HasParent $ index-p
          | isNothing last
          = if p==0
            then NoParent
            else go $ p-1
          | otherwise
          = case snd $ fromJust $ fromJust last ! p of
            NoParent -> NoParent
            HasParent poffset -> go $ p-poffset

hasParent :: VPPair -> Bool
hasParent node = isHasParent (snd node)

hasNoParent :: VPPair -> Bool
hasNoParent node = isNoParent (snd node)

isHasParent :: POffset -> Bool
isHasParent NoParent = False
isHasParent (HasParent _) = True

isNoParent :: POffset -> Bool
isNoParent NoParent = True
isNoParent (HasParent _) = False

fromHasParent :: POffset -> Integer
fromHasParent NoParent = error "POffset: NoParent"
fromHasParent (HasParent n) = n

parentIndex :: MountainRow -> Integer -> Integer
parentIndex row index = let node = row ! index in if isJust node && hasParent (fromJust node) then index - fromHasParent (snd $ fromJust node) else -1

uparentIndex :: UnfilledMountainRow -> Integer -> Integer
uparentIndex row index = let node = row ! index in if isJust node && isHasParent (snd $ fromJust node) then index - fromHasParent (snd $ fromJust node) else -1

fillParents :: Maybe MountainRow -> MountainRow -> MountainRow
fillParents last target = map go [0..ilength target-1]
  where go index
          | isNothing node = Nothing
          | otherwise = Just (fst $ fromJust $ target ! index, parent last target index)
          where node = target ! index

takeDifference :: MountainRow -> MountainRow
takeDifference row = map above [0..ilength row-1]
  where above index
          | isNothing node = Nothing
          | hasParent $ fromJust node = Just ((fst . fromJust $ node) - (fst . fromJust $ row ! parentIndex row index), NoParent)
          | any (\index2 -> parentIndex row index2 == index) [0..ilength row-1] = Just (1, NoParent)
          | otherwise = Nothing
          where node = row ! index

fillParentsAndBuildNextRow :: Maybe MountainRow -> MountainRow -> Mountain
fillParentsAndBuildNextRow last target
  | any (\node -> isJust node && (hasParent . fromJust $ node)) filledRow = filledRow : fillParentsAndBuildNextRow (Just filledRow) (takeDifference filledRow)
  | otherwise = [filledRow]
  where filledRow = fillParents last target

calcMountain :: Sequence -> Mountain
calcMountain seq = if not $ isValid seq then error "Invalid sequence" else fillParentsAndBuildNextRow Nothing $ map (Just . (, NoParent)) seq

extractSequence :: Mountain -> Sequence
extractSequence = map (fst . fromJust) . head

stringifyTest :: Mountain -> String
stringifyTest = join '\n' . reverse . map (\row -> join ' ' $ map (\index ->
  let node = row ! index in
  "(" ++ show (fst $ fromJust node) ++ "," ++ show index ++ ")"
  ) [0..ilength row-1])

stringifyMountain :: Mountain -> String
stringifyMountain = join '\n' . reverse . map (\row -> join ' ' $ map (\index ->
  let node = row ! index in
  if isNothing node
    then "(-,-)"
  else if hasNoParent $ fromJust node
    then "(" ++ show (fst $ fromJust node) ++ ",-)"
    else "(" ++ show (fst $ fromJust node) ++ "," ++ show (parentIndex row index) ++ ")"
  ) [0..ilength row-1])

stringifyUnfilledMountain :: UnfilledMountain -> String
stringifyUnfilledMountain = join '\n' . reverse . map (\row -> join ' ' $ map (\index ->
  let node = row ! index in
  if isNothing node
    then "(-,-)"
  else if isNothing $ fst $ fromJust node
    then "(?," ++ show (uparentIndex row index) ++ ")"
  else if isNoParent $ snd $ fromJust node
    then "(" ++ show (fromJust $ fst $ fromJust node) ++ ",-)"
    else "(" ++ show (fromJust $ fst $ fromJust node) ++ "," ++ show (uparentIndex row index) ++ ")"
  ) [0..ilength row-1])

badRoot :: Mountain -> Integer
badRoot mountain = if hasNoParent $ fromJust $ last $ mountain ! 0 then -1 else go 0
  where go y
          | hasNoParent $ fromJust $ last $ mountain ! (y+1) = parentIndex (mountain ! y) $ ilength (mountain ! y) - 1
          | otherwise = go (y+1)

goodPart :: Mountain -> Mountain
goodPart mountain = map (itake $ badRoot mountain) mountain

badPart :: Mountain -> Mountain
badPart mountain = map (init . idrop (badRoot mountain)) mountain

splitParts :: Mountain -> (Mountain, Mountain)
splitParts mountain = (goodPart mountain, badPart mountain)

hollowCopy :: (Mountain, Mountain, [Maybe VPPair]) -> Integer -> UnfilledMountain
hollowCopy (g,b,cut) m = map (\y -> map (go y) [0..width-1]) [0..height-1]
  where width = ilength $ b ! 0
        height = ilength b
        go y x =
          let row = b ! y
              cutNode = cut ! y
              cutNodeAbove = cut ! (y+1)
              node = row ! x in
          if x==0 && isJust cutNode && hasParent (fromJust cutNode) && hasParent (fromJust cutNodeAbove)
            then Just (Nothing, snd $ fromJust cutNode)
          else if isNothing node
              then Nothing
            else if hasParent $ fromJust node
              then if parentIndex row x < 0
                then Just (Nothing, HasParent $ fromHasParent (snd $ fromJust node) + m * width)
                else Just (Nothing, snd $ fromJust node)
              else Just $ first Just $ fromJust node

markUnfilled :: Mountain -> UnfilledMountain
markUnfilled = map (map (\node -> if isJust node then Just $ first Just (fromJust node) else Nothing))

markFilled :: UnfilledMountain -> Mountain
markFilled = map (map (\node -> if isJust node then Just $ first fromJust (fromJust node) else Nothing))

fillEmpty :: UnfilledMountain -> Mountain
fillEmpty mountain = markFilled $ foldl (\mountain y -> foldl (`go` y) mountain [0..width-1]) mountain [height-1,height-2..0]
  where width = ilength $ mountain ! 0
        height = ilength mountain
        go mountain y x = ireplaceAt2D mountain y x (
          if isNothing node
            then Nothing
          else if isNothing $ fst $ fromJust node
            then Just (Just $ fromJust (fst $ fromJust $ row ! uparentIndex row x) + fromJust (fst $ fromJust $ mountain ! (y+1) ! x), snd $ fromJust node)
            else node
          )
          where row = mountain ! y
                node = row ! x

expand :: Sequence -> Integer -> Sequence
expand [] n = []
expand seq _ | not (isValid seq) = error "Invalid sequence"
expand seq _ | last seq == 1 = init seq
expand seq n = extractSequence $ fillEmpty $ map concat $ transpose $ markUnfilled (map init mountain) : map (hollowCopy (g, b, map last mountain)) [1..n]
  where mountain = calcMountain seq
        (g,b) = splitParts mountain

calc :: (Integer -> Integer) -> Sequence -> Integer -> Integer
calc f [] n = n
calc f seq n = calc f (expand seq n) (f n)

calcDispStep :: (Integer -> Integer) -> Sequence -> Integer -> String
calcDispStep f [] n = "()[" ++ show n ++ "]\n= " ++ show n
calcDispStep f seq n = "(" ++ stringifySequence seq ++ ")\n[" ++ show n ++ "]> " ++ calcDispStep f (expand seq n) (f n)

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
  else if line == "exit"
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