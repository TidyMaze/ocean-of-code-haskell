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
    buyList = [(PTorpedo, torpedoCooldown state, 3), (PSilence, silenceCooldown state, 6), (PSonar, sonarCooldown state, 4), (PMine, mineCooldown state, 3)]
    found = find (\(power, count, max) -> count > 0) buyList :: Maybe (Power, Int, Int)

findStartCoord :: [Coord] -> Int -> Int -> Coord
findStartCoord waterCoords width height = minimumBy (comparing byManhattanToCenter) waterCoords
  where
    byManhattanToCenter = manhattan (Coord (width `div` 2) (height `div` 2))

findPositionFromHistory :: Precomputed -> S.Set Coord -> [Order] -> S.Set Coord
findPositionFromHistory !precomputed !lastCandidates !history = foldl' (execOrderBulk precomputed S.empty) lastCandidates history

execOrderBulk :: Precomputed -> S.Set Coord -> S.Set Coord -> Order -> S.Set Coord
execOrderBulk !precomputed visited !candidates !action = S.foldl' mergeCoordinates S.empty candidates
  where
    mergeCoordinates !acc !candidate = S.union acc $! S.fromList . toList $ execOrder precomputed visited action candidate

singleInSeqIf :: Bool -> Coord -> S.Set Coord
singleInSeqIf !cond coord =
  if cond
    then S.singleton coord
    else S.empty

enumerate = zip [0 ..]

{-# INLINE enumerate #-}
getSilenceRange :: Precomputed -> S.Set Coord -> Coord -> [(Coord, Direction, Int)]
getSilenceRange precomputed visitedSet c@(Coord cX cY) = concat [inNorth, inSouth, inWest, inEast]
  where
    inNorth = takeWhile valid $ map (\(i, y) -> (Coord cX y, N, i)) $ enumerate [cY,cY - 1 .. 0]
    inSouth = takeWhile valid $ map (\(i, y) -> (Coord cX y, S, i)) $ enumerate [cY,cY + 1 .. 14]
    inWest = takeWhile valid $ map (\(i, x) -> (Coord x cY, W, i)) $ enumerate [cX,cX - 1 .. 0]
    inEast = takeWhile valid $ map (\(i, x) -> (Coord x cY, E, i)) $ enumerate [cX,cX + 1 .. 14]
    valid (coord, dir, index) = coord == c || (index <= 4 && not (landMap precomputed V.! y coord V.! x coord) && coord `S.notMember` visitedSet)

execOrder :: Precomputed -> S.Set Coord -> Order -> Coord -> S.Set Coord
execOrder precomputed _ (Move direction _) c = singleInSeqIf (isWaterCoord (landMap precomputed) newC) newC
  where
    newC = addDirToCoord c direction
execOrder precomputed _ (Torpedo t) c = singleInSeqIf (inTorpedoRange precomputed c t) c
execOrder _ _ (Surface (Just sector)) c = singleInSeqIf (sector == sectorFromCoord c) c
execOrder _ _ (SonarResult sector True) c = singleInSeqIf (sector == sectorFromCoord c) c
execOrder _ _ (SonarResult sector False) c = singleInSeqIf (sector /= sectorFromCoord c) c
execOrder precomputed visited (Silence _) c = S.fromList $ map (\(c, _, _) -> c) $ getSilenceRange precomputed visited c
execOrder _ _ otherOrder state = S.singleton state

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

--instance Binary Precomputed
safeHead :: String -> [a] -> a
safeHead msg []     = error ("NO HEAD in " ++ msg)
safeHead msg (x:xs) = x

getMoveAction :: Precomputed -> State -> Maybe Coord -> (Order, [Coord], Int, Int, Coord)
getMoveAction precomputed state target = (action, newMyCoordHistory, updatedTorpedoCooldown, updatedSonarCooldown, afterCoord)
  where
    (action, newMyCoordHistory, powerBought) =
      case (maybeMoveWithDest, silenceCooldown state) of
        (Just (d, to), 0)
          | length (getUnvisitedWaterNeighborsDir (landMap precomputed) curCoord visitedSet) > 1 -> (Silence (Just (d, 1)), myCoordHistory state, Nothing)
        (Just (d, to), _) -> (Move d (Just powerToBuy), myCoordHistory state, Just powerToBuy)
          where powerToBuy = getPowerToBuy state
        (Nothing, _) -> (Surface Nothing, [], Nothing)
    (updatedTorpedoCooldown, updatedSonarCooldown) =
      case powerBought of
        Just PTorpedo -> (max (torpedoCooldown state - 1) 0, sonarCooldown state)
        Just PSonar -> (torpedoCooldown state, max (sonarCooldown state - 1) 0)
        _ -> (torpedoCooldown state, sonarCooldown state)
    afterCoord = maybe curCoord snd maybeMoveWithDest
    curCoord = safeHead "afterCoord" visited
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
    afterCoord = maybe (safeHead "afterCoord2" $ myCoordHistory state) snd maybeMoveWithDest
    maybeMoveWithDest = findMove precomputed (myCoordHistory state) Nothing

explosionDamages :: Coord -> Coord -> Int
explosionDamages landing dest =
  case diagDst dest landing of
    0 -> 2
    1 -> 1
    _ -> 0

getTorpedoAction :: Precomputed -> Maybe [Coord] -> Bool -> State -> Maybe Order
getTorpedoAction precomputed targets oppFound state =
  case (torpedoCooldown state, targets, oppFound) of
    (0, Just candidates, False) -> fmap Torpedo closestToTarget
      where closestToTarget = minByOption (manhattan after) (filter iCanShootSafely candidates)
            after = head $ myCoordHistory state
            iCanShootSafely closeTarget = iCanHitThisCloseCoord && notGettingHurt
              where
                iCanHitThisCloseCoord = inTorpedoRange precomputed after closeTarget
                notGettingHurt = not (inExplosionRange closeTarget after)
    (0, Just [realTarget], True) -> fmap Torpedo closestToTarget
      where after = head $ myCoordHistory state
            closestToTarget =
              fmap
                (\(c, dmgGiven, dmgReceived, diffDmg) -> c)
                (maxByOption (\(c, dmgGiven, dmgReceived, diffDmg) -> (dmgGiven, -dmgReceived)) (filter dontDoAnythingStupid (map getShootData (waterCoords precomputed))))
            dontDoAnythingStupid (c, dmgGiven, dmgReceived, diffDmg) = iCanShootIt && doNotSuicide && iDealDamages && canTakeALotIfIKill
              where
                iCanShootIt = inTorpedoRange precomputed after c
                doNotSuicide = dmgReceived < myLife state
                iDealDamages = dmgGiven > 0
                canTakeALotIfIKill = diffDmg > 0 || (dmgGiven >= oppLife state && dmgReceived < myLife state)
            getShootData c = (c, dmgGiven, dmgReceived, dmgGiven - dmgReceived)
              where
                dmgReceived = explosionDamages c after
                dmgGiven = explosionDamages c realTarget
    (0, Just [], _) -> Nothing
    (_, _, _) -> Nothing

groupBy :: Ord b => (a -> b) -> [a] -> Map.Map b [a]
groupBy f elems = Map.fromListWith (++) (map (\x -> (f x, [x])) elems)

getSonarAction :: Int -> [Coord] -> Maybe Order
getSonarAction cooldown _
  | cooldown > 0 = Nothing
getSonarAction _ [] = Nothing
getSonarAction _ candidates = Just (Sonar (Just (fst biggestSector)))
  where
    biggestSector = maximumBy (comparing (length . snd)) countedCandidatesBySector
    countedCandidatesBySector = Map.assocs (Main.groupBy sectorFromCoord candidates)

parseSonarResult lastSonarAction sonarResult = lastSonarAction >>= parseNew
  where
    parseNew (Sonar (Just sector)) = Just (SonarResult sector (sonarResult == "Y"))
    parseNew _ = Nothing

buildNewOpponentHistory sonarResultAction "NA" = maybeToList sonarResultAction
buildNewOpponentHistory sonarResultAction opponentOrders = maybeToList sonarResultAction ++ map fst (parseOrders opponentOrders)

getElapsedTime startTime = do
  endTime <- getCurrentTime
  let elapsed = diffUTCTime endTime startTime
  return (show (ceiling (realToFrac (toRational elapsed * 1000))) ++ "ms")

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

findAttackSequence :: Precomputed -> State -> Maybe ([Coord], Int) -> [([Order], [Coord], Int, Int)]
findAttackSequence _ _ Nothing = []
findAttackSequence _ _ (Just ([], _)) = []
findAttackSequence _ state _
  | torpedoCooldown state > 1 = []
findAttackSequence precomputed state (Just targets) = findAttackSequenceAfterMove precomputed targets (notMoving ++ movingOnce ++ silencingOnce)
  where
    curCoord = safeHead "curCoord3" $ myCoordHistory state
    visitedSet = S.fromList $ myCoordHistory state
    notMoving = [([], [curCoord], torpedoCooldown state)]
    movingOnce = map (\(d, newC) -> ([Move d (Just powerBought)], [newC], updatedCD)) neighbors
      where
        powerBought =
          if torpedoCooldown state > 0
            then PTorpedo
            else getPowerToBuy state
        updatedCD =
          case powerBought of
            PTorpedo -> max (torpedoCooldown state - 1) 0
            _        -> torpedoCooldown state
        neighbors = getUnvisitedWaterNeighborsDir (landMap precomputed) curCoord visitedSet
    silencingOnce =
      if silenceCooldown state > 0
        then []
        else map (\(newC, d, size) -> ([Silence (Just (d, size))], coordsBetween curCoord newC, torpedoCooldown state)) $ toList $ getSilenceRange precomputed visitedSet curCoord

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

findAttackSequenceAfterMove :: Precomputed -> ([Coord], Int) -> [([Order], [Coord], Int)] -> [([Order], [Coord], Int, Int)]
findAttackSequenceAfterMove precomputed (targets, minDmg) sequences = concatMap getDmg sequences
  where
    getDmg (orders, newCoords, 0) =
      map
        (\c ->
           let dmg =
                 case () of
                   _
                     | minDmg == 2 -> explosionDamages c (head targets)
                   _
                     | c `elem` targets -> minDmg
                   _ -> 0
            in (orders ++ [Torpedo c], newCoords, dmg, explosionDamages c curCoord))
        (filter (\c -> (minDmg == 2 && diagDst c (head targets) <= 1) || c `elem` targets) whereICanShoot)
      where
        whereICanShoot = Map.keys $ getTorpedoRange precomputed curCoord
        curCoord = last newCoords
    getDmg _ = []

findActionsDeprecated :: Precomputed -> State -> Maybe [Coord] -> Maybe [Coord] -> [Coord] -> Bool -> ([Order], [Coord], Maybe Order)
findActionsDeprecated precomputed afterParsingInputsState mySetOfShooting oppSetOfShooting opponentCandidates oppFound =
  (moveAction : maybeToList maybeTorpedoAction ++ maybeToList maybeSonarAction, endMyCoordHistory, maybeSonarAction)
  where
    moveTarget = oppSetOfShooting >>= minByOption (manhattan $ head $ myCoordHistory afterParsingInputsState)
    (moveAction, endMyCoordHistory, updatedTorpedoCooldown, updatedSonarCooldown, afterCoord) = getMoveAction precomputed afterParsingInputsState moveTarget
    stateAfterMove = afterParsingInputsState {myCoordHistory = afterCoord : endMyCoordHistory, torpedoCooldown = updatedTorpedoCooldown, sonarCooldown = updatedSonarCooldown}
    maybeTorpedoAction = getTorpedoAction precomputed oppSetOfShooting oppFound stateAfterMove
    maybeSonarAction = getSonarAction updatedSonarCooldown opponentCandidates

findCenterOfExplosion :: Precomputed -> [Coord] -> Maybe ([Coord], Int)
findCenterOfExplosion _ [x] = Just ([x], 2)
findCenterOfExplosion _ coords
  | length coords > 9 = Nothing
findCenterOfExplosion precomputed coords = asum [fromCandidates, fromAnyWater]
  where
    fromCandidates = mfilter (not . null . fst) (Just (filter (\c -> all (inExplosionRange c) coords) coords, 1))
    fromAnyWater = mfilter (not . null . fst) (Just (filter (\c -> all (inExplosionRange c) coords) (waterCoords precomputed), 1))

timeoutSample1 =
  "\"x\\156\\197\\151\\139V\\195 \\f@y\\173\\GS\\175\\253\\255\\US\\204\\239\\240\\203\\212vi\\225\\142X\\173G\\229\\148\\229\\\\\\154&@ 0c\\150\\242j\\156\\233\\158\\166\\132\\229\\215\\ESCc\\229\\241\\USm\\190yD\\207\\179yk\\179\\139\\213\\229\\&7\\244\\158F\\246\\252\\163\\205\\SUB\\244+\\240\\195\\147\\223\\246m\\150\\223\\142\\236\\181\\227P\\236\\217\\US|{\\194\\222\\DEL\\249X\\203K\\183<\\186e0\\148\\ETB\\240\\132v2%\\237\\136\\191I\\225#?\\148\\&3\\244\\132\\ETX\\216\\131\\157\\194W\\232\\147#\\244\\201\\t\\250\\228\\f}r\\129>\\185B_\\216*\\\\\\192\\EM\\156\\192\\DC1,\\227\\&7\\nGp\\STXgp\\SOHW\\240\\r\\254\\133\\GS\\216\\131\\131\\194\\NAK\\\\\\192\\EM,\\253\\191(\\156\\193\\ENQ\\\\\\193\\210\\159I\\225\\n.\\224\\fN\\224\\b\\150\\248\\204\\nGp\\STXgp\\SOHW\\176\\140\\231\\170p\\ENQ\\ETBp\\ACK'p\\EOTk\\237Q\\145\\t\\156\\193\\ENQ\\\\\\193\\&2\\158\\164p\\ENQ\\ETBp\\ACKS\\178\\159\\156\\a-n\\140\\187\\240\\ENQ\\FS\\192Z\\RSK\\n3\\143\\GS\\237\\DC3m\\221r]1\\238\\140\\v\\231-+\\178\\128+\\248\\ACK=r\\ENQS\\210\\SI\\227\\204u\\196u\\206}\\196}\\174\\229\\NAK\\230%a\\237\\FS)\\n\\243\\FS\\209\\242\\\"\\243\\SYN\\243\\DC2\\247=\\247\\&5\\247\\r\\247\\ENQ\\227\\194y\\175\\138\\188\\GSH\\234\\&1\\206\\\\\\a\\220\\199\\220\\231\\204c\\204s\\204\\227\\204\\243<\\135xn\\DEL\\247\\FS\\151\\194s\\147\\231\\234\\217s]xV\\152\\247$\\222\\163x\\207\\226=\\140\\247\\&4\\145\\247\\213\\213V\\221V\\253^\\131\\NAKw\\182{e\\247\\218\\170\\216\\254\\213\\174bU\\NAK\\183:\\r\\162\\241p4\\168Tq\\205k7v\\228\\DEL\\171/\\239\\170VSs\\159;{\\154\\190q\\DEL\\154\\209\\157t\\244'V\\156}\\142\\248\\&27nSs\\136\\149b\\233 V\\178\\242\\218\\200\\175\\220\\&93c\\181v\\145\\182\\150\\186\\254\\236V\\190\\&2\\248\\190H\\131\\246\\175jz\\ETX2\\235\\DC1\\141\""

timeoutSample1Pre =
  "\"x\\156\\165\\215mN\\132\\&0\\DLE\\NUL\\208\\178P\\160_\\236\\253o\\228\\177\\212\\r\\DC3\\205SV\\141\\252p\\242\\170\\t\\GS\\218\\206\\212\\148\\RS\\207Kz\\254L\\248\\134g\\188\\224\\140w\\\\p\\197\\rw<\\240qF\\231=]\\196\\ESC\\158\\241\\130\\&3\\222q\\193\\NAK7\\220\\241\\192\\145\\143\\223=<\\227\\ENQg\\188\\226\\r\\239\\184\\224\\138\\ESC\\238x\\224\\200g\\190\\136\\v\\206x\\197\\ESC\\222q\\193\\NAK7\\220\\241\\192\\&1\\DEL\\231\\185\\\\\\196\\140W\\188\\225\\138\\ESC\\238x\\224\\152\\159\\223\\205y\\228\\139\\184\\226\\rW\\220p\\199\\ETX\\199\\252\\226=\\DC3v\\159\\186\\238~G\\231m\\220\\240\\142\\v\\174\\184\\225\\142\\a\\142\\252\\226\\189\\tO\\216s\\232\\190v\\159\\184.\\230i\\220q\\193\\NAK7\\220\\241\\192\\145\\175u\\208:\\226\\185\\f/8c\\215\\205\\188\\140\\ENQW\\220p\\199\\ETXG~\\214u\\235\\162u&\\188\\224\\140\\221\\135\\174\\147y\\EM+n\\184\\227\\129#?\\251\\148u\\222\\186i\\157\\178.x\\142\\220g\\174\\139y\\212\\139\\216p\\199\\ETXG~\\222#\\236\\195\\246\\&1\\251\\130u\\216\\186g\\157\\240\\FS\\185\\239\\\\'\\243j\\ETB\\177\\227\\129\\SI\\254.a\\239\\GS\\246m\\251\\160}\\199:o]\\180nx\\206\\220\\151\\174\\163y\\SUB\\a>\\CANO\\216{\\149\\247\\DC2\\251\\188}\\213>f\\221\\183.ZG<w\\238S\\215\\209<\\141\\a1\\225\\171{\\138\\247\\STX\\251\\176}\\203\\186n\\GS\\180nx\\206\\220\\135\\174\\147y\\220?\\197\\233\\237y\\255\\145>\\158\\251\\&9z>\\211\\143\\195\\223=\\DEL\\FS\\158\\252\\US\\226\\233\\240\\227\\253_~\\245l\\248\\223\\DC3\\252\\221\\240+\\CAN\\192\\r\\\\\""

shortEncode :: Binary a => a -> String
shortEncode e = show $ Zlib.compress $ encode e

shortDecode :: Binary a => String -> a
shortDecode raw = decode $ Zlib.decompress (read raw :: LBS.ByteString)

findOrders precomputed afterParsingInputsState !myOldCandidates !oppOldCandidates = do
  let !opponentCandidates = findPositionFromHistory precomputed oppOldCandidates (opponentHistory afterParsingInputsState)
  let !myCandidates = findPositionFromHistory precomputed myOldCandidates (myHistory afterParsingInputsState)
  debug ("opp candidates (" ++ show (length opponentCandidates) ++ "): " ++ show (S.take 5 opponentCandidates))
  debug ("my candidates (" ++ show (length myCandidates) ++ "): " ++ show (S.take 5 myCandidates))
  let maybeOppListOfShooting = findCenterOfExplosion precomputed $ S.toList opponentCandidates
  let oppFound = length opponentCandidates == 1
  let maybeMyListOfShooting = findCenterOfExplosion precomputed $ S.toList myCandidates
  debug ("I think you are at " ++ show maybeOppListOfShooting)
  debug ("You think I'm at " ++ show maybeMyListOfShooting)
  let attackSeq =
        sortOn (\(orders, newCoords, damagesGiven, damagesTaken) -> (-damagesGiven, damagesTaken, length orders)) $
        filter (\(orders, newCoords, damagesGiven, damagesTaken) -> damagesTaken < myLife afterParsingInputsState && (damagesGiven > damagesTaken || damagesGiven >= oppLife afterParsingInputsState)) $
        findAttackSequence precomputed afterParsingInputsState maybeOppListOfShooting
  T.traceShowM $ "attackSeq" ++ show attackSeq
  let (!actions, endMyCoordHistory, maybeSonarAction) =
        case attackSeq of
          (x:_) -> trace "rushing" (orders, hist, maybeSonarAction)
            where (bestSeq, newCoords) = (\(a, b, c, d) -> (a, b)) . safeHead "bestSeq" $ attackSeq
                  orders = bestSeq ++ maybeToList (fmap (\(action, _, _, _, _) -> action) maybeMoveFallback)
                  maybeMoveFallback =
                    if any isMoveOrSurface bestSeq
                      then Nothing
                      else trace "fallback" (Just (getMoveActionNoTarget precomputed afterParsingInputsState {myCoordHistory = hist}))
                  isMoveOrSurface (Move _ _)  = True
                  isMoveOrSurface (Surface _) = True
                  isMoveOrSurface _           = False
                  hist = reverse newCoords ++ myCoordHistory afterParsingInputsState
                  maybeSonarAction = Nothing
          [] -> trace "deprecated" findActionsDeprecated precomputed afterParsingInputsState (fmap fst maybeMyListOfShooting) (fmap fst maybeOppListOfShooting) (S.toList opponentCandidates) oppFound
  let message = Msg (show (length opponentCandidates) ++ "/" ++ show (length myCandidates))
  let !resState = afterParsingInputsState {myCoordHistory = endMyCoordHistory, myHistory = actions, lastSonarAction = maybeSonarAction}
  let !out = intercalate "|" (map showOrder (actions ++ [message]))
  return (out, resState, myCandidates, opponentCandidates)

gameLoop :: Precomputed -> State -> S.Set Coord -> S.Set Coord -> IO ()
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
  let afterParsingInputsState =
        oldState
          { myCoordHistory = nub $ Coord x y : myCoordHistory oldState
          , opponentHistory = buildNewOpponentHistory (parseSonarResult (lastSonarAction oldState) sonarresult) opponentOrders
          , torpedoCooldown = torpedocooldown
          , sonarCooldown = sonarcooldown
          , silenceCooldown = silencecooldown
          , mineCooldown = minecooldown
          , myLife = myLife
          , oppLife = oppLife
          }
  debug $ show $ shortEncode afterParsingInputsState
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
  debug $ show $ shortEncode (waterCoords, landMap)
  send $ show startX ++ " " ++ show startY
  let state =
        State
          {myHistory = [], opponentHistory = [], myCoordHistory = [], lastSonarAction = Nothing, torpedoCooldown = 3, sonarCooldown = 4, silenceCooldown = 6, mineCooldown = 3, myLife = 6, oppLife = 6}
  let wc = S.fromList waterCoords
  gameLoop precomputed state wc wc

--  debug (show precomputed)
perf :: IO ()
perf = do
  (orders, _, _, _) <- findOrders precomputed state S.empty S.empty
  print $ orders
  print "done"
  return ()
  where
    precomputed = buildPrecomputed waterCoords $ V.fromList $ map V.fromList landMap
    state = shortDecode timeoutSample1
    (waterCoords, landMap) = shortDecode timeoutSample1Pre :: ([Coord], [[Bool]])

--  print precomputed
--  print state
main :: IO ()
main = game
