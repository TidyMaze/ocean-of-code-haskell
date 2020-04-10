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

isWaterCoord :: [[Bool]] -> Coord -> Bool
isWaterCoord landMap c = isInBoard c && not (landMap !! y c !! x c)

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

findPositionFromHistory :: Precomputed -> [Order] -> S.Set Coord
findPositionFromHistory !precomputed !history = foldl' (execOrderBulk precomputed S.empty) (S.fromList (waterCoords precomputed)) history

execOrderBulk :: Precomputed -> S.Set Coord -> S.Set Coord -> Order -> S.Set Coord
execOrderBulk !precomputed visited !candidates !action = S.foldl' mergeCoordinates S.empty candidates
  where
    mergeCoordinates acc candidate = S.union acc (execOrder precomputed visited action candidate)

singleInSetIf :: Bool -> Coord -> S.Set Coord
singleInSetIf !cond coord =
  S.fromList $!
  if cond
    then [coord]
    else []

enumerate = zip [0 ..]

getSilenceRange :: Precomputed -> S.Set Coord -> Coord -> S.Set (Coord, Direction, Int)
getSilenceRange precomputed visitedSet c@(Coord cX cY) = S.fromList $ foldl' union [] [inNorth, inSouth, inWest, inEast]
  where
    !inNorth = takeWhile valid $ map (\(i, y) -> (Coord cX y, N, i)) $ enumerate [cY,cY - 1 .. 0]
    !inSouth = takeWhile valid $ map (\(i, y) -> (Coord cX y, S, i)) $ enumerate [cY,cY + 1 .. 14]
    !inWest = takeWhile valid $ map (\(i, x) -> (Coord x cY, W, i)) $ enumerate [cX,cX - 1 .. 0]
    !inEast = takeWhile valid $ map (\(i, x) -> (Coord x cY, E, i)) $ enumerate [cX,cX + 1 .. 14]
    valid (coord, dir, index) = coord == c || (index <= 4 && coord `S.notMember` visitedSet && not (landMap precomputed !! y coord !! x coord))

execOrder :: Precomputed -> S.Set Coord -> Order -> Coord -> S.Set Coord
execOrder precomputed _ (Move direction _) c = singleInSetIf (isWaterCoord (landMap precomputed) newC) newC
  where
    newC = addDirToCoord c direction
execOrder precomputed _ (Torpedo t) c = singleInSetIf (inTorpedoRange precomputed c t) c
execOrder _ _ (Surface (Just sector)) c = singleInSetIf (sector == sectorFromCoord c) c
execOrder _ _ (SonarResult sector True) c = singleInSetIf (sector == sectorFromCoord c) c
execOrder _ _ (SonarResult sector False) c = singleInSetIf (sector /= sectorFromCoord c) c
execOrder precomputed visited (Silence _) c = S.map (\(c, _, _) -> c) (getSilenceRange precomputed visited c)
execOrder _ _ otherOrder state = S.fromList [state]

toOpponentInput :: Coord -> Order -> Order
toOpponentInput _ (Move d _)      = Move d Nothing
toOpponentInput coord (Surface _) = Surface (Just (sectorFromCoord coord))
toOpponentInput _ (Silence _)     = Silence Nothing
toOpponentInput _ (Mine _)        = Mine Nothing
toOpponentInput _ other           = other

getWaterNeighbors :: [[Bool]] -> Coord -> [(Direction, Coord)]
getWaterNeighbors landMap c = filter (\(d, dest) -> isWaterCoord landMap dest) neighbors
  where
    computeNeighbor d = (d, addDirToCoord c d)
    neighbors = map computeNeighbor [N, E, S, W]

getUnvisitedWaterNeighborsDir landMap c visited = filter unvisitedWater (getWaterNeighbors landMap c)
  where
    unvisitedWater (d, dest) = dest `S.notMember` visited

comparingMaybe :: Ord a => Maybe a -> Maybe a -> Ordering
comparingMaybe (Just _) Nothing = LT
comparingMaybe Nothing (Just _) = GT
comparingMaybe a b              = compare a b

coordToIndex c = y c * 15 + x c
{-# INLINE coordToIndex #-}

indexToCoord i = Coord (i `mod` 15) (i `div` 15)
{-# INLINE indexToCoord #-}

convertKey (i, Just v) = Just (indexToCoord i, v)
convertKey _           = Nothing
{-# INLINE convertKey #-}

bfs :: [Coord] -> (Coord -> Maybe Int -> [Coord]) -> Coord -> Map.Map Coord Int
bfs waterCoords getNeighbors c =
  unsafePerformIO $ do
    dist <- newArray (0, 15 * 15 - 1) Nothing :: IO (IOArray Int (Maybe Int))
    writeArray dist (coordToIndex c) (Just 0)
    bfsAux dist getNeighbors waterCoords

bfsAux :: IOArray Int (Maybe Int) -> (Coord -> Maybe Int -> [Coord]) -> [Coord] -> IO (Map.Map Coord Int)
bfsAux !dist _ [] = fmap (Map.fromList . mapMaybe convertKey) (getAssocs dist)
bfsAux !dist !getNeighbors !q = do
  !withDists <- mapM (sequence . (\x -> (x, getDist x))) q
  let !(u, du) = minimumBy cmpDist withDists
  let !updatedQ = delete u q
  !newValues <- catMaybes <$> mapM (findWhatToUpdate du) (filter (`elem` q) (getNeighbors u du))
  !writes <- mapM_ (\(c, d) -> writeArray dist (coordToIndex c) (Just d)) newValues
  bfsAux dist getNeighbors updatedQ
  where
    getDist :: Coord -> IO (Maybe Int)
    getDist c = readArray dist (coordToIndex c)
    cmpDist (c1, d1) (c2, d2) = comparingMaybe d1 d2
    findWhatToUpdate :: Maybe Int -> Coord -> IO (Maybe (Coord, Int))
    findWhatToUpdate du v = do
      maybeOld <- getDist v
      return $!
        case (fmap (+ 1) du, maybeOld) of
          (Just alt, Just old) -> Just (v, min alt old)
          (Nothing, Just old) -> Nothing
          (Just alt, Nothing) -> Just (v, alt)
          (Nothing, Nothing) -> Nothing

bfsLimited :: Int -> [Coord] -> (Coord -> [Coord]) -> Coord -> Map.Map Coord Int
bfsLimited limit waterCoords getNeighbors = bfs waterCoords neighborsWithDist
  where
    neighborsWithDist coord Nothing = []
    neighborsWithDist coord (Just dist)
      | dist >= 4 = []
    neighborsWithDist coord (Just dist)
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
    , landMap       :: ![[Bool]]
    }
  deriving (Show, Generic)

instance Binary Precomputed

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

buildNewOpponentHistory oldOpponentHistory sonarResultAction "NA" = oldOpponentHistory ++ maybeToList sonarResultAction
buildNewOpponentHistory oldOpponentHistory sonarResultAction opponentOrders = oldOpponentHistory ++ maybeToList sonarResultAction ++ map fst (parseOrders opponentOrders)

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

findAttackSequence :: Precomputed -> State -> Maybe Coord -> [([Order], [Coord], Int, Int)]
findAttackSequence _ _ Nothing = []
findAttackSequence _ state _
  | torpedoCooldown state > 1 = []
findAttackSequence precomputed state (Just target) = findAttackSequenceAfterMove precomputed target (notMoving ++ movingOnce ++ silencingOnce)
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
        else map (\(newC, d, size) -> ([Silence (Just (d, size))], coordsBetween curCoord newC, torpedoCooldown state)) silenceCoords
      where
        silenceCoords = S.toList $ getSilenceRange precomputed visitedSet curCoord

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

findAttackSequenceAfterMove :: Precomputed -> Coord -> [([Order], [Coord], Int)] -> [([Order], [Coord], Int, Int)]
findAttackSequenceAfterMove precomputed target sequences = concatMap getDmg sequences
  where
    getDmg (orders, newCoords, 0) = map (\c -> (orders ++ [Torpedo c], newCoords, explosionDamages c target, explosionDamages c curCoord)) (filter ((<= 1) . diagDst target) whereICanShoot)
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

findCenterOfExplosion :: Precomputed -> [Coord] -> Maybe [Coord]
findCenterOfExplosion _ [x] = Just [x]
findCenterOfExplosion _ coords
  | length coords > 9 = Nothing
findCenterOfExplosion precomputed coords = asum [fromCandidates, fromAnyWater]
  where
    fromCandidates = mfilter (not . null) (Just $ filter (\c -> all (inExplosionRange c) coords) coords)
    fromAnyWater = mfilter (not . null) (Just $ filter (\c -> all (inExplosionRange c) coords) (waterCoords precomputed))

timeoutSample1 = "\"x\\156\\133\\148a\\146\\131 \\fF\\ETX\\168`\\NAK\\SO\\181\\251\\187\\247\\191N\\NAK\\t\\234\\171\\217\\205\\DLE3\\143\\134|I\\EM\\NAK\\169\\246\\SYN/\\251r\\\"A\\215\\197\\134\\250\\f\\151U\\DC3\\a\\205;6\\\\+\\161\\219\\163k\\199\\147\\192\\170\\216\\160\\138\\253\\169\\219r\\151\\147\\166U5{\\209\\169\\&5\\219+^\\210\\190Vm)\\156G\\189\\158\\216\\236\\183\\197\\185\\197\\ENQ\\188\\130\\&3\\184\\180\\248\\&28\\131W\\240\\STXf\\156\\193\\t\\FSQ\\135\\156\\192\\156\\147}0\\174\\224\\f.\\200#g\\176\\181\\159\\141X\\254\\137\\204c\\USV\\223\\156\\139\\247\\194{WN\\224\\b\\158\\192#\\244\\201\\DC38\\130U\\175\\CAN\\FS\\193\\DC3x\\EOT\\235\\v\\150\\r\\SO`\\SI\\214\\183\\168\\CAN\\172\\150\\193+x1\\216\\129=X\\251{\\EM\\172\\243\\204\\224d\\176\\254?\\209\\224\\t\\172\\241\\231hu\\255\\n\\213\\232\\183x\\184\\156q\\208i\\234w\\232L\\217\\221m\\238\\247\\DC4\\215S\\\\\\219\\214\\159\\155_S|\\DC3P\\247=\\205=UrwA\\166\\248\\239J\\DEL\\137\\201\\243T\\254\\222\\238\\147\\DLE\\197\\170\\223-\\CAN\\172\\ETB0~\\NUL\\213A\\a\\183\""

timeoutSample1Pre = "\"x\\156\\157\\214Yr\\131\\&0\\f\\NULP\\155\\GS/\\228\\254\\199\\233\\205:]\\212\\194K\\201G\\249\\209<'\\ETX2\\216\\146S\\250\\188\\222\\210\\235+\\227\\SOH\\143x\\194\\&3\\222\\240\\142\\v\\174\\184\\225\\142\\143\\239h\\222\\249&\\SOx\\196\\DC3\\158\\241\\134w\\\\p\\197\\rw\\FS\\243\\&1\\207\\225&\\142x\\193+\\222\\240\\142\\v\\174\\184\\225\\142#\\DEL\\223\\171y\\142\\&7q\\193+\\222\\240\\142\\v\\174\\184\\225\\142#\\DEL\\215\\181\\235\\\"<\\224\\DC1\\ESCg\\188\\224\\NAK\\ETB\\\\q\\195\\GS\\199|\\220\\151\\174\\235\\240\\128G\\236<\\140\\v^q\\193\\NAK7\\220q\\204'\\158\\147p\\198\\238\\v\\243\\&4\\174x\\195;.\\184\\226\\134;\\142\\249\\196s\\DC3\\206\\216}\\237{v\\RS\\198\\r\\239\\184\\224\\138\\ESC\\238\\&8\\230c\\221\\183nZ\\135\\220\\215\\225\\t\\207\\216\\239\\228<\\141;.\\184\\226\\134;\\142\\249\\218\\a\\172\\171\\214\\169\\240\\132\\253.\\230m,\\184\\226\\134;\\142\\252\\237[\\246\\SOH\\235\\170u\\201u\\227{5\\207r\\DC3+n\\184\\227\\200\\223s\\131}\\215>f_\\176\\174\\186\\238]\\ETB\\190g\\243\\174\\&7\\177\\225\\142\\SI\\254\\151\\176\\231\\b\\251\\178}\\206>a\\157\\181N\\185\\207\\221\\a\\174+\\191\\147\\243\\&4v|0\\158\\176\\231$\\207\\GS\\246q\\251\\160}\\196:l\\GSs\\159\\251\\157\\156\\135\\241 &\\236\\&9\\239\\174O\\219\\231\\236\\DC3\\214Y\\247\\129\\235\\200\\247l\\158\\143\\223\\152\\191r\\204\\231#\\245#\\253y1\\156\\175\\195q\\135\\211\\240\\199\\208\\229\\198<\\242\\244\\211\\227\\a7\\195\\207\\153<\\255t\\GS\\206$\\248z\\248z\\147\\DEL\\SI\\191\\ETX\\240\\182\\f\\154\""


shortEncode :: Binary a => a -> String
shortEncode e = show $ Zlib.compress $ encode e

shortDecode :: Binary a => String -> a
shortDecode raw = decode $ Zlib.decompress (read raw :: LBS.ByteString)

findOrders precomputed afterParsingInputsState = do
  debug ("history " ++ show (length $ myHistory afterParsingInputsState) ++ " " ++ show (length $ opponentHistory afterParsingInputsState))
  let !opponentCandidates = S.toList $! findPositionFromHistory precomputed (opponentHistory afterParsingInputsState)
  debug ("opp candidates (" ++ show (length opponentCandidates) ++ "): " ++ show (take 5 opponentCandidates))
  let !myCandidates = S.toList $! findPositionFromHistory precomputed (myHistory afterParsingInputsState)
  debug ("my candidates (" ++ show (length myCandidates) ++ "): " ++ show (take 5 myCandidates))
  let maybeOppBaryWithMeanDev = findCenterOfExplosion precomputed opponentCandidates
  let oppFound = length opponentCandidates == 1
  let maybeMyBaryWithMeanDev = findCenterOfExplosion precomputed myCandidates
  debug ("I think you are at " ++ show maybeOppBaryWithMeanDev)
  debug ("You think I'm at " ++ show maybeMyBaryWithMeanDev)
  debug ("Closest waters is " ++ show maybeOppBaryWithMeanDev)
  let attackSeq =
        sortOn (\(orders, newCoords, damagesGiven, damagesTaken) -> (-damagesGiven, damagesTaken, length orders)) $
        findAttackSequence
          precomputed
          afterParsingInputsState
          (if oppFound
             then Just (safeHead "oppFound" opponentCandidates)
             else Nothing)
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
          [] -> trace "deprecated" findActionsDeprecated precomputed afterParsingInputsState maybeMyBaryWithMeanDev maybeOppBaryWithMeanDev opponentCandidates oppFound
  let message = Msg (show (length opponentCandidates) ++ "/" ++ show (length myCandidates))
  let !resState = afterParsingInputsState {myCoordHistory = endMyCoordHistory, myHistory = myHistory afterParsingInputsState ++ actions, lastSonarAction = maybeSonarAction}
  let !out = intercalate "|" (map showOrder (actions ++ [message]))
  return (out, resState)

gameLoop :: Precomputed -> State -> IO ()
gameLoop !precomputed !oldState = do
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
  debug ("third line " ++ opponentOrders)
  let afterParsingInputsState =
        oldState
          { myCoordHistory = nub $ Coord x y : myCoordHistory oldState
          , opponentHistory = buildNewOpponentHistory (opponentHistory oldState) (parseSonarResult (lastSonarAction oldState) sonarresult) opponentOrders
          , torpedoCooldown = torpedocooldown
          , sonarCooldown = sonarcooldown
          , silenceCooldown = silencecooldown
          , mineCooldown = minecooldown
          , myLife = myLife
          , oppLife = oppLife
          }
--  debug $ show $ shortEncode afterParsingInputsState
  (out, resState) <- findOrders precomputed afterParsingInputsState
  send out
  gameLoop precomputed resState

buildPrecomputed waterCoords landMap = Precomputed {coordsInRange = Map.fromList mapping, waterCoords = waterCoords, landMap = landMap}
  where
    mapping = map (\x -> (x, getTorpedoRange waterCoords landMap x)) waterCoords
    getTorpedoRange waterCoords landMap = bfsLimited torpedoRange waterCoords fn
      where
        fn = map snd . getWaterNeighbors landMap

game :: IO ()
game = do
  hSetBuffering stdout NoBuffering -- DO NOT REMOVE
  input_line <- getLine
  let input = words input_line
  let width = read (input !! 0) :: Int
  let height = read (input !! 1) :: Int
  let myid = read (input !! 2) :: Int
  !landMap <- replicateM height $ map (== 'x') <$> getLine
  startTime <- getCurrentTime
  let allCoords = [Coord x y | x <- [0 .. 14], y <- [0 .. 14]]
  let !waterCoords = filter (isWaterCoord landMap) allCoords :: [Coord]
--  debug $ show $ shortEncode (waterCoords, landMap)
  let !precomputed = buildPrecomputed waterCoords landMap
  let Coord startX startY = findStartCoord waterCoords width height
  endTime <- getCurrentTime
  let elapsed = diffUTCTime endTime startTime
  debug ("spent " ++ show (realToFrac (toRational elapsed * 1000)) ++ " ms")
  send $ show startX ++ " " ++ show startY
  let state =
        State
          {myHistory = [], opponentHistory = [], myCoordHistory = [], lastSonarAction = Nothing, torpedoCooldown = 3, sonarCooldown = 4, silenceCooldown = 6, mineCooldown = 3, myLife = 6, oppLife = 6}
  gameLoop precomputed state

--  debug (show precomputed)
perf :: IO ()
perf = do
--  print precomputed
--  print state
  (orders, _) <- findOrders precomputed state
  print $ orders
  print "done"
  return ()
  where
    precomputed = buildPrecomputed waterCoords landMap
    state = shortDecode timeoutSample1
    (waterCoords, landMap) = shortDecode timeoutSample1Pre :: ([Coord], [[Bool]])

main :: IO ()
main = perf
