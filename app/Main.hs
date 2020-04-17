{-# LANGUAGE BangPatterns   #-}
{-# LANGUAGE TupleSections  #-}
{-# OPTIONS_GHC -XStrict #-}
{-# LANGUAGE DeriveGeneric  #-}
{-# LANGUAGE NamedFieldPuns #-}

module Main where

import           Control.Applicative    ((<$>))
import           Control.Monad
import           Data.Array.IO
import           Data.Binary
import qualified Data.ByteString.Lazy   as LBS
import           Data.Foldable
import           Data.List
import qualified Data.List.Split        as Split
import qualified Data.Map.Strict        as Map
import           Data.Maybe
import           Data.Ord
import qualified Data.Set               as S
import           Data.Time.Clock
import qualified Data.Vector            as V
import           Debug.Trace            as T
import           GHC.Generics           (Generic)
import           System.IO
import           System.IO.Unsafe

import qualified Codec.Compression.Zlib as Zlib

data Direction
  = N
  | S
  | W
  | E
  deriving (Read, Enum, Show, Eq, Ord, Generic)

instance Binary Direction

data Power
  = PTorpedo
  | PSonar
  | PSilence
  | PMine
  deriving (Show, Eq, Generic)

instance Binary Power

showPower PTorpedo = "TORPEDO"
showPower PSonar   = "SONAR"
showPower PSilence = "SILENCE"
showPower PMine    = "MINE"

data Coord =
  Coord
    { x :: {-# UNPACK #-}!Int
    , y :: {-# UNPACK #-}!Int
    }
  deriving (Show, Eq, Ord, Generic)

instance Binary Coord

data Order
  = Move Direction (Maybe Power)
  | Torpedo Coord
  | Msg String
  | Surface (Maybe Int)
  | Silence (Maybe (Direction, Int))
  | Sonar (Maybe Int)
  | SonarResult Int Bool
  | Mine (Maybe Direction)
  | Trigger Coord
  deriving (Eq, Generic)

instance Binary Order

instance Show Order where
  show = showOrder

instance Read Order where
  readsPrec _ s = [(parsed, drop eaten s)]
    where
      (parsed, eaten) = parseOrder s

showOrder (Move dir power) = "MOVE " ++ show dir ++ maybe "" ((" " ++) . showPower) power
showOrder (Torpedo (Coord x y)) = "TORPEDO " ++ show x ++ " " ++ show y
showOrder (Msg message) = "MSG " ++ message
showOrder (Surface sector) = "SURFACE" ++ maybe "" ((" " ++) . show) sector
showOrder (Silence dirSize) = "SILENCE" ++ maybe "" (\(d, s) -> " " ++ show d ++ " " ++ show s) dirSize
showOrder (Sonar sector) = "SONAR" ++ maybe "" ((" " ++) . show) sector
showOrder (SonarResult sector result) = "SONARRESULT " ++ show sector ++ " " ++ show result
showOrder (Mine dir) = "MINE" ++ maybe "" ((" " ++) . show) dir
showOrder (Trigger (Coord x y)) = "TRIGGER " ++ show x ++ " " ++ show y

splitOn :: (a -> Bool) -> [a] -> [[a]]
splitOn _ [] = []
splitOn f l@(x:xs)
  | f x = splitOn f xs
  | otherwise =
    let (h, t) = break f l
     in h : splitOn f t

splitEq :: Eq a => a -> [a] -> [[a]]
splitEq e = splitOn (== e)

debug :: String -> IO ()
debug = hPutStrLn stderr

send :: String -> IO ()
send = putStrLn

parsePower :: String -> Power
parsePower "TORPEDO" = PTorpedo
parsePower "SONAR"   = PSonar
parsePower "SILENCE" = PSilence
parsePower "MINE"    = PMine

isSpace = (== ' ')

trim = dropWhileEnd isSpace . dropWhile isSpace

parseMove rawDir = Move (read rawDir :: Direction) Nothing

parseTorpedo rawX rawY = Torpedo (Coord (read rawX :: Int) (read rawY :: Int))

parseTrigger rawX rawY = Trigger (Coord (read rawX :: Int) (read rawY :: Int))

parseSurface rawSector = Surface (Just (read rawSector :: Int))

parseSonar rawSector = Sonar (Just (read rawSector :: Int))

parseOrder :: String -> (Order, Int)
parseOrder o = (process (preprocess o), length o)
  where
    preprocess raw = splitEq ' ' $ trim raw
    process ["MOVE", rawDir]        = parseMove rawDir
    process ["SURFACE", rawSector]  = parseSurface rawSector
    process ["TORPEDO", rawX, rawY] = parseTorpedo rawX rawY
    process ["MSG", message]        = Msg message
    process ["SILENCE"]             = Silence Nothing
    process ["SONAR", rawSector]    = parseSonar rawSector
    process ["MINE"]                = Mine Nothing
    process ["TRIGGER", rawX, rawY] = parseTrigger rawX rawY

parseOrders orderRaw = map parseOrder (splitEq '|' orderRaw)

sectorFromCoord (Coord x y) = y `div` 5 * 3 + x `div` 5 + 1

{-# INLINE sectorFromCoord #-}
addDirToCoord (Coord x y) dir = Coord (x + oX) (y + oY)
  where
    (oX, oY) = getOffset dir

{-# INLINE addDirToCoord #-}
getOffset :: Direction -> (Int, Int)
getOffset N = (0, -1)
getOffset S = (0, 1)
getOffset W = (-1, 0)
getOffset E = (1, 0)

{-# INLINE getOffset #-}
isInBoard (Coord x y) = y >= 0 && y < 15 && x >= 0 && x < 15

{-# INLINE isInBoard #-}
manhattan to from = abs (x to - x from) + abs (y to - y from)

{-# INLINE manhattan #-}
diagDst to from = (dx + dy) - min dx dy
  where
    dx = abs (x from - x to)
    dy = abs (y from - y to)

{-# INLINE diagDst #-}
baryMeanDev :: Fractional a => [Coord] -> Maybe (Coord, a)
baryMeanDev [] = Nothing
baryMeanDev coords = fmap (\b -> (b, fromIntegral (foldl' (distToB b) 0 coords) / fromIntegral (length coords))) maybeB
  where
    distToB b a x = diagDst b x + a
    maybeB = fmap (\(bx, by) -> Coord (round bx) (round by)) (bary coords)

bary :: Fractional a => [Coord] -> Maybe (a, a)
bary [] = Nothing
bary coords = Just (avgX, avgY)
  where
    size = length coords
    avgX = fromIntegral (sum (map x coords)) / fromIntegral size
    avgY = fromIntegral (sum (map y coords)) / fromIntegral size

isWaterCoord :: V.Vector (V.Vector Bool) -> Coord -> Bool
isWaterCoord landMap c = isInBoard c && not (landMap V.! y c V.! x c)

getPowerToBuy :: State -> Power
getPowerToBuy state = maybe PTorpedo fst3 found
  where
    fst3 (a, b, c) = a
    buyList = [(PTorpedo, torpedoCooldown state, 3), (PSonar, sonarCooldown state, 4), (PSilence, silenceCooldown state, 6), (PMine, mineCooldown state, 3)]
    found = find (\(power, count, max) -> count > 0) buyList :: Maybe (Power, Int, Int)

findStartCoord :: [Coord] -> Int -> Int -> Coord
findStartCoord waterCoords width height = minimumBy (comparing byManhattanToCenter) waterCoords
  where
    byManhattanToCenter = manhattan (Coord (width `div` 2) (height `div` 2))

-- TODO: use oppLife to deduce location after torpedo (ignore complex cases)
findPositionFromHistory :: Precomputed -> [(Coord, S.Set Coord)] -> [Order] -> [(Coord, S.Set Coord)]
findPositionFromHistory !precomputed !lastCandidates !history = foldl' (execOrderBulk precomputed) lastCandidates history

execOrderBulk :: Precomputed -> [(Coord, S.Set Coord)] -> Order -> [(Coord, S.Set Coord)]
execOrderBulk !precomputed !candidates !action = concatMap mergeCoordinates candidates
  where
    mergeCoordinates (!candidate, visited) = execOrder precomputed visited action candidate

singleInSeqIf :: Bool -> Coord -> S.Set Coord -> [(Coord, S.Set Coord)]
singleInSeqIf !cond coord visited = [(coord, S.insert coord visited) | cond]

enumerate = zip [0 ..]

{-# INLINE enumerate #-}
getSilenceRange :: Precomputed -> S.Set Coord -> Coord -> [(Coord, Direction, Int)]
getSilenceRange precomputed visitedSet c@(Coord cX cY) = (c, N, 0) : concat [inNorth, inSouth, inWest, inEast]
  where
    inNorth = takeWhile valid $ map (\(i, y) -> (Coord cX y, N, i + 1)) $ enumerate [cY - 1,cY - 2 .. 0]
    inSouth = takeWhile valid $ map (\(i, y) -> (Coord cX y, S, i + 1)) $ enumerate [cY + 1,cY + 2 .. 14]
    inWest = takeWhile valid $ map (\(i, x) -> (Coord x cY, W, i + 1)) $ enumerate [cX - 1,cX - 2 .. 0]
    inEast = takeWhile valid $ map (\(i, x) -> (Coord x cY, E, i + 1)) $ enumerate [cX + 1,cX + 2 .. 14]
    valid (coord, dir, index) = index <= 4 && not (landMap precomputed V.! y coord V.! x coord) && coord `S.notMember` visitedSet

execOrder :: Precomputed -> S.Set Coord -> Order -> Coord -> [(Coord, S.Set Coord)]
execOrder precomputed visited (Move direction _) c = singleInSeqIf (isWaterCoord (landMap precomputed) newC && newC `S.notMember` visited) newC visited
  where
    newC = addDirToCoord c direction
execOrder precomputed visited (Torpedo t) c = singleInSeqIf (inTorpedoRange precomputed c t) c visited
execOrder _ visited (Surface (Just sector)) c = [(c, S.singleton c) | sector == sectorFromCoord c]
execOrder _ visited (SonarResult sector True) c = singleInSeqIf (sector == sectorFromCoord c) c visited
execOrder _ visited (SonarResult sector False) c = singleInSeqIf (sector /= sectorFromCoord c) c visited
execOrder precomputed visited (Silence _) c = map (\(d, _, _) -> (d, S.union (S.fromList $ coordsBetween c d) visited)) $ getSilenceRange precomputed visited c
execOrder _ visited otherOrder state = [(state, visited)]

toOpponentInput :: Coord -> Order -> Order
toOpponentInput _ (Move d _)      = Move d Nothing
toOpponentInput coord (Surface _) = Surface (Just (sectorFromCoord coord))
toOpponentInput _ (Silence _)     = Silence Nothing
toOpponentInput _ (Mine _)        = Mine Nothing
toOpponentInput _ other           = other

getWaterNeighbors :: V.Vector (V.Vector Bool) -> Coord -> [(Direction, Coord)]
getWaterNeighbors landMap c = filter (\(d, dest) -> isWaterCoord landMap dest) neighbors
  where
    computeNeighbor d = (d, addDirToCoord c d)
    neighbors = map computeNeighbor [N, E, S, W]

getUnvisitedWaterNeighborsDir landMap c visited = filter unvisitedWater (getWaterNeighbors landMap c)
  where
    unvisitedWater (d, dest) = dest `S.notMember` visited

comparingMaybe :: Ord a => Maybe a -> Maybe a -> Ordering
comparingMaybe (Just _) Nothing  = LT
comparingMaybe Nothing (Just _)  = GT
comparingMaybe Nothing Nothing   = EQ
comparingMaybe (Just a) (Just b) = compare a b

{-# INLINE comparingMaybe #-}
coordToIndex c = y c * 15 + x c

{-# INLINE coordToIndex #-}
indexToCoord i = Coord (i `mod` 15) (i `div` 15)

{-# INLINE indexToCoord #-}
convertKey (i, v)
  | v == maxBound = Nothing
convertKey (i, v) = Just (indexToCoord i, v)

{-# INLINE convertKey #-}
bfs :: [Coord] -> (Coord -> Int -> [Coord]) -> Coord -> Map.Map Coord Int
bfs waterCoords getNeighbors c =
  unsafePerformIO $ do
    dist <- newArray (0, 15 * 15 - 1) maxBound :: IO (IOArray Int Int)
    writeArray dist (coordToIndex c) 0
    bfsAux dist getNeighbors (S.singleton (0, c))

bfsAux :: IOArray Int Int -> (Coord -> Int -> [Coord]) -> S.Set (Int, Coord) -> IO (Map.Map Coord Int)
bfsAux !dist !getNeighbors !q =
  case S.minView q of
    Nothing -> fmap (Map.fromList . mapMaybe convertKey) (getAssocs dist)
    Just ((du, u), q') -> do
      !updatedQ <- foldM (updateNeighbor du) q' (getNeighbors u du)
      bfsAux dist getNeighbors updatedQ
      where getDist :: Coord -> IO Int
            getDist c = readArray dist (coordToIndex c)
            updateNeighbor :: Int -> S.Set (Int, Coord) -> Coord -> IO (S.Set (Int, Coord))
            updateNeighbor du vq n = do
              old <- getDist n
              let alt = du + 1
              if alt < old
                then do
                  let vq' = S.delete (old, n) vq
                  writeArray dist (coordToIndex n) alt
                  return $ S.insert (alt, n) vq'
                else pure vq

bfsLimited :: Int -> [Coord] -> (Coord -> [Coord]) -> Coord -> Map.Map Coord Int
bfsLimited limit waterCoords getNeighbors = bfs waterCoords neighborsWithDist
  where
    neighborsWithDist coord dist
      | dist >= 4 = []
    neighborsWithDist coord dist
      | dist < 4 = getNeighbors coord

findMove :: Precomputed -> [Coord] -> Maybe Coord -> Maybe (Direction, Coord)
findMove precomputed visited target = listToMaybe (sortOn (\(dir, d) -> criteria target d) neighbors)
  where
    visitedSet = S.fromList visited
    neighbors = getUnvisitedWaterNeighborsDir (landMap precomputed) (head visited) visitedSet
    fn x _ = map snd (getUnvisitedWaterNeighborsDir (landMap precomputed) x visitedSet)
    criteria (Just o) d = (byLonguestPath d, fromMaybe 1000 (distancesToO Map.!? d))
      where
        distancesToO = bfs (waterCoords precomputed) fn o
    criteria Nothing d = (byLonguestPath d, 0)
    byLonguestPath d =
      if null coordDistances
        then 0
        else -distanceToFarestCoord
      where
        coordDistances = bfs (waterCoords precomputed) fn d
        distanceToFarestCoord = snd (maximumBy (comparing snd) (Map.toList coordDistances))

isSilence :: Order -> Bool
isSilence (Silence _) = True
isSilence _           = False

minByOption _ [] = Nothing
minByOption f xs = Just (minimumBy (comparing f) xs)

maxByOption _ [] = Nothing
maxByOption f xs = Just (maximumBy (comparing f) xs)

torpedoRange = 4

getTorpedoRange precomputed from = fromMaybe Map.empty (coordsInRange precomputed Map.!? from)

inTorpedoRange :: Precomputed -> Coord -> Coord -> Bool
inTorpedoRange precomputed from dest = dest `Map.member` getTorpedoRange precomputed from

inExplosionRange center dest = diagDst dest center <= 1

data Precomputed =
  Precomputed
    { coordsInRange :: !(Map.Map Coord (Map.Map Coord Int))
    , waterCoords   :: ![Coord]
    , landMap       :: !(V.Vector (V.Vector Bool))
    }
  deriving (Show, Generic)

getMoveAction :: Precomputed -> State -> Maybe Coord -> [Coord] -> (Order, [Coord], Int, Int, Coord)
getMoveAction precomputed state target myCandidates = (action, newMyCoordHistory, updatedTorpedoCooldown, updatedSonarCooldown, afterCoord)
  where
    (action, newMyCoordHistory, powerBought) =
      case (maybeMoveWithDest, silenceCooldown state) of
        (Just (d, to), 0)
          | length myCandidates <= 10 && length (getUnvisitedWaterNeighborsDir (landMap precomputed) curCoord visitedSet) > 1 -> (Silence (Just (d, 1)), myCoordHistory state, Nothing)
        (Just (d, to), _) -> (Move d (Just powerToBuy), myCoordHistory state, Just powerToBuy)
          where powerToBuy = getPowerToBuy state
        (Nothing, _) -> (Surface Nothing, [], Nothing)
    (updatedTorpedoCooldown, updatedSonarCooldown) =
      case powerBought of
        Just PTorpedo -> (max (torpedoCooldown state - 1) 0, sonarCooldown state)
        Just PSonar -> (torpedoCooldown state, max (sonarCooldown state - 1) 0)
        _ -> (torpedoCooldown state, sonarCooldown state)
    afterCoord = maybe curCoord snd maybeMoveWithDest
    curCoord = head visited
    visited = myCoordHistory state
    visitedSet = S.fromList visited
    maybeMoveWithDest = findMove precomputed visited target

getMoveActionNoTarget :: Precomputed -> State -> (Order, [Coord], Int, Int, Coord)
getMoveActionNoTarget precomputed state = (action, newMyCoordHistory, updatedTorpedoCooldown, updatedSonarCooldown, afterCoord)
  where
    (action, newMyCoordHistory, powerBought) =
      case (maybeMoveWithDest, silenceCooldown state) of
        (Just (d, to), _) -> (Move d (Just powerToBuy), myCoordHistory state, Just powerToBuy)
          where powerToBuy = getPowerToBuy state
        (Nothing, _) -> (Surface Nothing, [], Nothing)
    (updatedTorpedoCooldown, updatedSonarCooldown) =
      case powerBought of
        Just PTorpedo -> (max (torpedoCooldown state - 1) 0, sonarCooldown state)
        Just PSonar -> (torpedoCooldown state, max (sonarCooldown state - 1) 0)
        _ -> (torpedoCooldown state, sonarCooldown state)
    afterCoord = maybe (head $ myCoordHistory state) snd maybeMoveWithDest
    maybeMoveWithDest = findMove precomputed (myCoordHistory state) Nothing

explosionDamages :: Coord -> Coord -> Int
explosionDamages landing dest =
  case diagDst dest landing of
    0 -> 2
    1 -> 1
    _ -> 0

groupBy :: Ord b => (a -> b) -> [a] -> Map.Map b [a]
groupBy f elems = Map.fromListWith (++) (map (\x -> (f x, [x])) elems)

getSonarAction :: Int -> [Coord] -> Maybe Order
getSonarAction cooldown _
  | cooldown > 0 = Nothing
getSonarAction _ [] = Nothing
getSonarAction _ candidates =
  if length biggestSectors < 2
    then Nothing
    else Just (Sonar (Just (fst $ head biggestSectors)))
  where
    biggestSectors = sortOn (negate . length . snd) countedCandidatesBySector
    countedCandidatesBySector = Map.assocs (Main.groupBy sectorFromCoord candidates)

parseSonarResult lastSonarAction sonarResult = lastSonarAction >>= parseNew
  where
    parseNew (Sonar (Just sector)) = Just (SonarResult sector (sonarResult == "Y"))
    parseNew _ = Nothing

buildNewOpponentHistory :: Maybe Order -> [Order] -> [Order]
buildNewOpponentHistory sonarResultAction orders = maybeToList sonarResultAction ++ orders

data State =
  State
    { opponentHistory :: ![Order]
    , myCoordHistory  :: ![Coord]
    , myHistory       :: ![Order]
    , lastSonarAction :: !(Maybe Order)
    , torpedoCooldown :: {-# UNPACK #-}!Int
    , sonarCooldown   :: {-# UNPACK #-}!Int
    , silenceCooldown :: {-# UNPACK #-}!Int
    , mineCooldown    :: {-# UNPACK #-}!Int
    , myLife          :: {-# UNPACK #-}!Int
    , oppLife         :: {-# UNPACK #-}!Int
    }
  deriving (Show, Eq, Generic)

instance Binary State

decrementCooldown powerBought power currentCooldown =
  if powerBought == power
    then max 0 (currentCooldown - 1)
    else currentCooldown

applyOrder :: Order -> State -> State
applyOrder o@(Move dir (Just powerBought)) state =
  state
    { myCoordHistory = newC : myCoordHistory state
    , myHistory = myHistory state ++ [o]
    , torpedoCooldown = decrementCooldown powerBought PTorpedo (torpedoCooldown state)
    , sonarCooldown = decrementCooldown powerBought PSonar (sonarCooldown state)
    , silenceCooldown = decrementCooldown powerBought PSilence (silenceCooldown state)
    , mineCooldown = decrementCooldown powerBought PMine (mineCooldown state)
    }
  where
    newC = addDirToCoord (head $ myCoordHistory state) dir
applyOrder o@(Silence (Just (dir, size))) state = state {myCoordHistory = reverse (coordsBetween curCoord newC) ++ myCoordHistory state, myHistory = myHistory state ++ [o]}
  where
    curCoord = head $ myCoordHistory state
    newC = foldl' addDirToCoord curCoord (replicate size dir)

getMovingOnce precomputed state oldOrders = map prepareAction neighbors
  where
    curCoord = head $ myCoordHistory state
    visitedSet = S.fromList $ myCoordHistory state
    prepareAction (d, newC) = (oldOrders ++ [newAction], applyOrder newAction state)
      where
        newAction = Move d (Just powerBought)
    powerBought =
      if torpedoCooldown state > 0
        then PTorpedo
        else getPowerToBuy state
    neighbors = getUnvisitedWaterNeighborsDir (landMap precomputed) curCoord visitedSet

getSilencingOnce precomputed state oldOrders =
  if silenceCooldown state > 0
    then []
    else let visitedSet = S.fromList $ myCoordHistory state
             curCoord = head $ myCoordHistory state
             prepareAction (newC, d, size) = (oldOrders ++ [newAction], applyOrder newAction state)
               where
                 newAction = Silence (Just (d, size))
          in map prepareAction $ toList $ getSilenceRange precomputed visitedSet curCoord

-- TODO: move + silence and silence + move
findAttackSequence :: Precomputed -> State -> Maybe ([Coord], Int) -> [([Order], State, Int, Int)]
findAttackSequence _ _ Nothing = []
findAttackSequence _ _ (Just ([], _)) = []
findAttackSequence _ state _
  | torpedoCooldown state > 1 = []
findAttackSequence precomputed state (Just targets) = findAttackSequenceAfterMove precomputed targets (notMoving ++ movingOnce ++ silencingOnce ++ moveSilence)
  where
    notMoving = [([], state)]
    movingOnce = getMovingOnce precomputed state []
    silencingOnce = getSilencingOnce precomputed state []
    moveSilence = concatMap (\(orders, state') -> getSilencingOnce precomputed state' orders) $ getMovingOnce precomputed state []

--    silenceMove = concatMap (\(orders, state') -> getMovingOnce precomputed state' orders) $ getSilencingOnce precomputed state []
coordsBetween (Coord fx fy) (Coord tx ty) = res
  where
    !res =
      [ Coord x y
      | x <-
          if tx >= fx
            then [fx .. tx]
            else [fx,fx - 1 .. tx]
      , y <-
          if ty >= fy
            then [fy .. ty]
            else [fy,fy - 1 .. ty]
      ]

findAttackSequenceAfterMove :: Precomputed -> ([Coord], Int) -> [([Order], State)] -> [([Order], State, Int, Int)]
findAttackSequenceAfterMove precomputed (targets, minDmg) = concatMap getDmg
  where
    getDmg (orders, state)
      | torpedoCooldown state == 0 =
        map
          (\c ->
             let dmg =
                   case () of
                     _
                       | minDmg == 2 -> explosionDamages c (head targets)
                     _
                       | c `elem` targets -> minDmg
                     _ -> 0
              in (orders ++ [Torpedo c], state, dmg, explosionDamages c curCoord))
          (filter (\c -> (minDmg == 2 && diagDst c (head targets) <= 1) || c `elem` targets) whereICanShoot)
      where
        whereICanShoot = Map.keys $ getTorpedoRange precomputed curCoord
        curCoord = head $ myCoordHistory state
    getDmg _ = []

findActionsDeprecated :: Precomputed -> State -> Maybe [Coord] -> Maybe [Coord] -> [Coord] -> [Coord] -> Bool -> ([Order], [Coord], Maybe Order)
findActionsDeprecated precomputed afterParsingInputsState mySetOfShooting oppSetOfShooting opponentCandidates myCandidates oppFound =
  (moveAction : (maybeToList maybeTorpedoAction ++ maybeToList maybeSonarAction), endMyCoordHistory, maybeSonarAction)
  where
    moveTarget = oppSetOfShooting >>= minByOption (manhattan $ head $ myCoordHistory afterParsingInputsState)
    (moveAction, endMyCoordHistory, updatedTorpedoCooldown, updatedSonarCooldown, afterCoord) = getMoveAction precomputed afterParsingInputsState moveTarget myCandidates
    stateAfterMove = afterParsingInputsState {myCoordHistory = afterCoord : endMyCoordHistory, torpedoCooldown = updatedTorpedoCooldown, sonarCooldown = updatedSonarCooldown}
    maybeTorpedoAction = Nothing
    maybeSonarAction = getSonarAction updatedSonarCooldown opponentCandidates

findCenterOfExplosion :: Precomputed -> [Coord] -> Maybe ([Coord], Int)
findCenterOfExplosion _ [x] = Just ([x], 2)
findCenterOfExplosion _ coords
  | length coords > 9 = Nothing
findCenterOfExplosion precomputed coords = asum [fromCandidates, fromAnyWater]
  where
    fromCandidates = mfilter (not . null . fst) (Just (filter (\c -> all (inExplosionRange c) coords) coords, 1))
    fromAnyWater = mfilter (not . null . fst) (Just (filter (\c -> all (inExplosionRange c) coords) (waterCoords precomputed), 1))

findOrders precomputed afterParsingInputsState !myOldCandidates !oppOldCandidates = do
  let !opponentCandidates = findPositionFromHistory precomputed oppOldCandidates (opponentHistory afterParsingInputsState)
  let !myCandidates = findPositionFromHistory precomputed myOldCandidates (myHistory afterParsingInputsState)
  let oppCandidatesUnique = nub $ map fst opponentCandidates
  let myCandidatesUnique = nub $ map fst myCandidates
  debug ("opp candidates (" ++ show (length oppCandidatesUnique) ++ "): " ++ show (take 5 oppCandidatesUnique) ++ " < " ++ show (length opponentCandidates))
  debug ("my candidates (" ++ show (length myCandidatesUnique) ++ "): " ++ show (take 5 myCandidatesUnique) ++ " < " ++ show (length myCandidates))
  let maybeOppListOfShooting = findCenterOfExplosion precomputed oppCandidatesUnique
  let oppFound = length opponentCandidates == 1
  let maybeMyListOfShooting = findCenterOfExplosion precomputed myCandidatesUnique
  debug ("I think you are at " ++ show maybeOppListOfShooting)
  debug ("You think I'm at " ++ show maybeMyListOfShooting)
  let attackSeq =
        sortOn (\(orders, newCoords, damagesGiven, damagesTaken) -> (-damagesGiven, damagesTaken, length orders)) $
        filter (\(orders, newCoords, damagesGiven, damagesTaken) -> damagesTaken < myLife afterParsingInputsState && (damagesGiven > damagesTaken || damagesGiven >= oppLife afterParsingInputsState)) $ {-(damagesGiven == 2 || damagesGiven >= oppLife afterParsingInputsState || myLife afterParsingInputsState >= 2 + oppLife afterParsingInputsState) &&-}
        findAttackSequence precomputed afterParsingInputsState maybeOppListOfShooting
  let (!actions, endMyCoordHistory, maybeSonarAction) =
        case attackSeq of
          (x:_) -> trace "rushing" (orders, hist, maybeSonarAction)
            where (bestSeq, newState) = (\(a, b, c, d) -> (a, b)) . head $ attackSeq
                  orders = bestSeq ++ maybeToList (fmap (\(action, _, _, _, _) -> action) maybeMoveFallback)
                  maybeMoveFallback =
                    if any isMoveOrSurface bestSeq
                      then Nothing
                      else trace "fallback" (Just (getMoveActionNoTarget precomputed afterParsingInputsState {myCoordHistory = hist}))
                  isMoveOrSurface (Move _ _)  = True
                  isMoveOrSurface (Surface _) = True
                  isMoveOrSurface _           = False
                  hist = myCoordHistory newState
                  maybeSonarAction = Nothing
          [] ->
            trace
              "deprecated"
              findActionsDeprecated
              precomputed
              afterParsingInputsState
              (fmap fst maybeMyListOfShooting)
              (fmap fst maybeOppListOfShooting)
              oppCandidatesUnique
              myCandidatesUnique
              oppFound
  let message = Msg (show (length oppCandidatesUnique) ++ "/" ++ show (length myCandidatesUnique))
  let !resState = afterParsingInputsState {myCoordHistory = endMyCoordHistory, myHistory = actions, lastSonarAction = maybeSonarAction}
  let !out = intercalate "|" (map showOrder (actions ++ [message]))
  return (out, resState, myCandidates, opponentCandidates)

--  T.traceShowM $ "attackSeq" ++ show attackSeq
getSonar :: [Order] -> Maybe Order
getSonar []               = Nothing
getSonar (s@(Sonar _):xs) = Just s
getSonar (_:xs)           = getSonar xs

gameLoop :: Precomputed -> State -> [(Coord, S.Set Coord)] -> [(Coord, S.Set Coord)] -> IO ()
gameLoop !precomputed !oldState !myOldCandidates !oppOldCandidates = do
  input_line <- getLine
  let input = words input_line
  let x = read (input !! 0) :: Int
  let y = read (input !! 1) :: Int
  let myLife = read (input !! 2) :: Int
  let oppLife = read (input !! 3) :: Int
  let torpedocooldown = read (input !! 4) :: Int
  let sonarcooldown = read (input !! 5) :: Int
  let silencecooldown = read (input !! 6) :: Int
  let minecooldown = read (input !! 7) :: Int
  input_line <- getLine
  let sonarresult = input_line :: String
  opponentOrders <- getLine
  startTime <- getCurrentTime
  let parsedOppOrders =
        if opponentOrders == "NA"
          then []
          else map fst (parseOrders opponentOrders)
  let afterParsingInputsState =
        oldState
          { myCoordHistory = nub $ Coord x y : myCoordHistory oldState
          , myHistory = myHistory oldState ++ maybe [] (\(Sonar (Just sector)) -> [SonarResult sector (sector == sectorFromCoord (Coord x y))]) (getSonar parsedOppOrders)
          , opponentHistory = buildNewOpponentHistory (parseSonarResult (lastSonarAction oldState) sonarresult) parsedOppOrders
          , torpedoCooldown = torpedocooldown
          , sonarCooldown = sonarcooldown
          , silenceCooldown = silencecooldown
          , mineCooldown = minecooldown
          , myLife = myLife
          , oppLife = oppLife
          }
  (!out, !resState, !myNewCandidates, !oppNewCandidates) <- findOrders precomputed afterParsingInputsState myOldCandidates oppOldCandidates
  endTime <- getCurrentTime
  let elapsed = diffUTCTime endTime startTime
  let spentString = show (realToFrac (toRational elapsed * 1000)) ++ " ms"
  debug ("spent " ++ spentString)
  send out
  gameLoop precomputed resState myNewCandidates oppNewCandidates

buildPrecomputed waterCoords landMap = Precomputed {coordsInRange = Map.fromList mapping, waterCoords = waterCoords, landMap = landMap}
  where
    mapping = map (\x -> (x, getTorpedoRange waterCoords landMap x)) waterCoords
    getTorpedoRange waterCoords landMap = bfsLimited torpedoRange waterCoords fn
      where
        fn = map snd . getWaterNeighbors landMap

instance Binary a => Binary (V.Vector a) where
  put v = put $ V.toList v
  get = fmap V.fromList get

game :: IO ()
game = do
  hSetBuffering stdout NoBuffering
  input_line <- getLine
  let input = words input_line
  let width = read (input !! 0) :: Int
  let height = read (input !! 1) :: Int
  let myid = read (input !! 2) :: Int
  !landMap <- fmap (V.fromList . map V.fromList) $ replicateM height $ map (== 'x') <$> getLine
  startTime <- getCurrentTime
  let allCoords = [Coord x y | x <- [0 .. 14], y <- [0 .. 14]]
  let !waterCoords = filter (isWaterCoord landMap) allCoords :: [Coord]
  let !precomputed = buildPrecomputed waterCoords landMap
  let Coord startX startY = findStartCoord waterCoords width height
  endTime <- getCurrentTime
  let elapsed = diffUTCTime endTime startTime
  debug ("spent " ++ show (realToFrac (toRational elapsed * 1000)) ++ " ms")
  send $ show startX ++ " " ++ show startY
  let state =
        State
          {myHistory = [], opponentHistory = [], myCoordHistory = [], lastSonarAction = Nothing, torpedoCooldown = 3, sonarCooldown = 4, silenceCooldown = 6, mineCooldown = 3, myLife = 6, oppLife = 6}
  let wc = map (\c -> (c, S.singleton c)) waterCoords
  gameLoop precomputed state wc wc

--  print precomputed
--  print state
main :: IO ()
main = game
