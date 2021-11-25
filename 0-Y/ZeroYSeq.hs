{-# LANGUAGE TupleSections #-}

-- HexirpさんのBashicu.hsを参考にしました

module ZeroYSeq where
import Data.List
    ( elemIndex,
      genericDrop,
      genericLength,
      genericTake,
      singleton,
      transpose )
import Data.Maybe ( fromJust, isJust, isNothing )
import Data.Bifunctor ( Bifunctor(first) )

(!) :: [a] -> Integer -> a
[] ! _ = undefined
(x:xs) ! 0 = x
(x:xs) ! n = xs ! (n-1)

infixl 9 !

ilength :: [a] -> Integer
ilength xs = genericLength xs :: Integer

type Sequence = [Integer]
data POffset = NoParent | HasParent Integer
type VPPair = (Integer,POffset)
type MountainRow = [Maybe VPPair]
type Mountain = [MountainRow]
type UnfilledVPPair = (Maybe Integer,POffset)
type UnfilledMountainRow = [Maybe UnfilledVPPair]
type UnfilledMountain = [UnfilledMountainRow]

splitString :: Char -> String -> [String]
splitString char "" = []
splitString char str =
  case elemIndex char str of
    Just index -> take index str : splitString char (drop (index+1) str)
    Nothing -> [str]

joinString :: Char -> [String] -> String
joinString char [] = ""
joinString char [str] = str
joinString char (str:strs) = str ++ singleton char ++ joinString char strs

parseSequence :: String -> Sequence
parseSequence input = map (\x -> read x :: Integer) $ splitString ',' input

stringifySequence :: Sequence -> String
stringifySequence seq = joinString ',' $ map show seq

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

extractSequence :: MountainRow -> Sequence
extractSequence = map (fst . fromJust)

stringifyTest :: Mountain -> String
stringifyTest = joinString '\n' . reverse . map (\row -> joinString ' ' $ map (\index ->
  let node = row ! index in
  "(" ++ show (fst $ fromJust node) ++ "," ++ show index ++ ")"
  ) [0..ilength row-1])

stringifyMountain :: Mountain -> String
stringifyMountain = joinString '\n' . reverse . map (\row -> joinString ' ' $ map (\index ->
  let node = row ! index in
  if isNothing node
    then "(-,-)"
  else if hasNoParent $ fromJust node
    then "(" ++ show (fst $ fromJust node) ++ ",-)"
    else "(" ++ show (fst $ fromJust node) ++ "," ++ show (parentIndex row index) ++ ")"
  ) [0..ilength row-1])

stringifyUnfilledMountain :: UnfilledMountain -> String
stringifyUnfilledMountain = joinString '\n' . reverse . map (\row -> joinString ' ' $ map (\index ->
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
goodPart mountain = map (genericTake $ badRoot mountain) mountain

badPart :: Mountain -> Mountain
badPart mountain = map (init . genericDrop (badRoot mountain)) mountain

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

fillEmpty :: UnfilledMountainRow -> MountainRow -> MountainRow
fillEmpty row rowAbove = foldl go [] $ zip row [0..]
  where go acc (Nothing, _) = acc ++ [Nothing]
        go acc (Just (Just v, p), _) = acc ++ [Just (v, p)]
        go acc (Just (Nothing, p), x) = acc ++ [Just (fst (fromJust $ acc ! uparentIndex row x) + fst (fromJust $ rowAbove ! x), p)]

expand :: Sequence -> Integer -> Sequence
expand [] n = []
expand seq _ | not (isValid seq) = error "Invalid sequence"
expand seq _ | last seq == 1 = init seq
expand seq n = extractSequence $ foldr (fillEmpty . concat) undefined $ transpose $ markUnfilled (map init mountain) : map (hollowCopy (g, b, map last mountain)) [1..n]
  where mountain = calcMountain seq
        (g,b) = splitParts mountain

calc :: (Integer -> Integer) -> Sequence -> Integer -> Integer
calc f [] n = n
calc f seq n = calc f (expand seq n) (f n)

calcSteps :: (Integer -> Integer) -> Sequence -> Integer -> [(Sequence, Integer)]
calcSteps f [] n = [([], n)]
calcSteps f seq n = (seq, n) : calcSteps f (expand seq n) (f n)