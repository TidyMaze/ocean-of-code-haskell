{-# LANGUAGE BangPatterns   #-}
{-# LANGUAGE TupleSections  #-}
{-# OPTIONS_GHC -XStrict #-}
{-# LANGUAGE DeriveGeneric  #-}
{-# LANGUAGE NamedFieldPuns #-}

module Main where

import           Control.Monad
import           Data.Binary
import           Data.Foldable
import           Data.List
import qualified Data.Map.Strict as Map
import           Data.Maybe
import           Data.Ord
import qualified Data.Set        as S
import           Data.Time.Clock
import qualified Data.Vector     as V
import           Debug.Trace     as T
import           GHC.Generics    (Generic)
import           System.IO
import qualified Data.ByteString.Lazy as LBS
import qualified Data.List.Split as Split

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

findPositionFromHistory :: Precomputed -> [Order] -> S.Set Coord
findPositionFromHistory !precomputed !history = foldl' (execOrderBulk precomputed []) (S.fromList (waterCoords precomputed)) history

execOrderBulk :: Precomputed -> [Coord] -> S.Set Coord -> Order -> S.Set Coord
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

getSilenceRange :: Precomputed -> [Coord] -> Coord -> S.Set (Coord, Direction, Int)
getSilenceRange precomputed visited c@(Coord cX cY) = S.unions [inNorth, inSouth, inWest, inEast]
  where
    !inNorth = S.fromList $ takeWhile valid $ map (\(i, y) -> (Coord cX y, N, i)) $ enumerate [cY,cY - 1 .. 0]
    !inSouth = S.fromList $ takeWhile valid $ map (\(i, y) -> (Coord cX y, S, i)) $ enumerate [cY,cY + 1 .. 14]
    !inWest = S.fromList $ takeWhile valid $ map (\(i, x) -> (Coord x cY, W, i)) $ enumerate [cX,cX - 1 .. 0]
    !inEast = S.fromList $ takeWhile valid $ map (\(i, x) -> (Coord x cY, E, i)) $ enumerate [cX,cX + 1 .. 14]
    valid (coord, dir, index) = coord == c || (index <= 4 && coord `S.notMember` visitedSet && not (landMap precomputed V.! y coord V.! x coord))
    !visitedSet = S.fromList visited

execOrder :: Precomputed -> [Coord] -> Order -> Coord -> S.Set Coord
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

getWaterNeighbors :: V.Vector (V.Vector Bool) -> Coord -> [(Direction, Coord)]
getWaterNeighbors landMap c = filter (\(d, dest) -> isWaterCoord landMap dest) neighbors
  where
    computeNeighbor d = (d, addDirToCoord c d)
    neighbors = map computeNeighbor [N, E, S, W]

getUnvisitedWaterNeighborsDir landMap c visited = filter unvisitedWater (getWaterNeighbors landMap c)
  where
    unvisitedWater (d, dest) = dest `S.notMember` visitedSet
    visitedSet = S.fromList visited

bfs :: [Coord] -> (Coord -> Maybe Int -> [Coord]) -> Coord -> Map.Map Coord Int
bfs waterCoords getNeighbors c = aux initDist initQ
  where
    initDist = Map.fromList [(c, 0)]
    initQ = waterCoords
    aux :: Map.Map Coord Int -> [Coord] -> Map.Map Coord Int
    aux !dist [] = dist
    aux !dist !q = aux newDist updatedQ
      where
        u = minimumBy (comparing (\x -> fromMaybe 1000 (dist Map.!? x))) q :: Coord
        updatedQ = filter (/= u) q
        du = dist Map.!? u
        newValues = Map.fromList (mapMaybe findWhatToUpdate (filter (`elem` q) (getNeighbors u du)))
        newDist = newValues `Map.union` dist
        maybeAlt = fmap (+ 1) du :: Maybe Int
        findWhatToUpdate v =
          case (maybeAlt, dist Map.!? v) of
            (Just alt, Just old) -> Just (v, min alt old)
            (Nothing, Just old)  -> Nothing
            (Just alt, Nothing)  -> Just (v, alt)
            (Nothing, Nothing)   -> Nothing

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
    neighbors = getUnvisitedWaterNeighborsDir (landMap precomputed) (head visited) visited
    fn x _ = map snd (getUnvisitedWaterNeighborsDir (landMap precomputed) x visited)
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
  deriving (Show)

safeHead :: String -> [a] -> a
safeHead msg []     = error ("NO HEAD in " ++ msg)
safeHead msg (x:xs) = x

getMoveAction :: Precomputed -> State -> Maybe Coord -> (Order, [Coord], Int, Int, Coord)
getMoveAction precomputed state target = (action, newMyCoordHistory, updatedTorpedoCooldown, updatedSonarCooldown, afterCoord)
  where
    (action, newMyCoordHistory, powerBought) =
      case (maybeMoveWithDest, silenceCooldown state) of
        (Just (d, to), 0)
          | length (getUnvisitedWaterNeighborsDir (landMap precomputed) curCoord visited) > 1 -> (Silence (Just (d, 1)), myCoordHistory state, Nothing)
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
    { opponentHistory :: {-# UNPACK #-}![Order]
    , myCoordHistory  :: {-# UNPACK #-}![Coord]
    , myHistory       :: {-# UNPACK #-}![Order]
    , lastSonarAction :: {-# UNPACK #-}!(Maybe Order)
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
        neighbors = getUnvisitedWaterNeighborsDir (landMap precomputed) curCoord (myCoordHistory state)
    silencingOnce =
      if silenceCooldown state > 0
        then []
        else map (\(newC, d, size) -> ([Silence (Just (d, size))], coordsBetween curCoord newC, torpedoCooldown state)) silenceCoords
      where
        silenceCoords = S.toList $ getSilenceRange precomputed (myCoordHistory state) curCoord

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

timeoutSample1 = "x\156\173TY\174\195 \f\244\146\208\210\190\191\222\255<\189J\143Q\214\NUL\DC3 H\175\SYNV4\142\&3\RSc+D\193>$\148\SO\227\217\250\&1%\176s\158\250\216\201\206\&1M|\241+\153\215\205\212\206L\250\222\&4\204\186\162\148rX\155X%)\147*O\181HG\179\&6D\ESC\150\SUB\223\193\184\223\170L{\a\177\221\170s\167\&7\154\205\GS\216\DLE\t\211]\155G\200;*\198C)V\159\139\EM\141\247@1\175\&3\ENQSr{J\181T\139\246\130&\254\NUL?\SOH?\NUL[\192w\192\&7\192\ACK\240\SO\CAN\175\NAK\183P\NUL3\245\r\227<x\n`\ENQ\188\SOH\206z\223\&1t\184\&4\174\206\&9<\253f\241\198\NAKmz\141\206>\173\168\227\196\NUL\142)\STX\133\201\167PS\172v\233\179,\DC4\226\163\163\210\157\&0\239\&9\203x\228}V~AaQ\233\152\202p\164S>z\145\160\139w\184\162\242\144\&0f\147y3\194\211\187\132\193\245X\132/'\"\224T]\135\253\193$\212\167\148\221=\223\254\DEL\251\171\231\n#g(\150\CAN\221_\241z\193=W\246v?Vv\EOTl\244\139\200\191\130\253\v{\SYN\a\a"

shortEncode :: Binary a => a -> String
shortEncode e = show $ Zlib.compress $ encode e

shortDecode :: Binary a => String -> a
shortDecode raw = decode $ Zlib.decompress (read raw :: LBS.ByteString)

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
  startTime <- getCurrentTime
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
  debug $ shortEncode afterParsingInputsState
  debug ("history " ++ show (length $ myHistory afterParsingInputsState) ++ " " ++ show (length $ opponentHistory afterParsingInputsState))
  let !opponentCandidates = S.toList $! findPositionFromHistory precomputed (opponentHistory afterParsingInputsState)
  debug ("opp candidates (" ++ show (length opponentCandidates) ++ "): " ++ show (take 5 opponentCandidates))
  spentTime1 <- getElapsedTime startTime
  debug ("opp: " ++ spentTime1)
  let !myCandidates = S.toList $! findPositionFromHistory precomputed (myHistory afterParsingInputsState)
  debug ("my candidates (" ++ show (length myCandidates) ++ "): " ++ show (take 5 myCandidates))
  spentTime2 <- getElapsedTime startTime
  debug ("me: " ++ spentTime2)
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
  spentTime <- getElapsedTime startTime
  let message = Msg (show (length opponentCandidates) ++ "/" ++ show (length myCandidates) ++ " " ++ spentTime)
  let resState = afterParsingInputsState {myCoordHistory = endMyCoordHistory, myHistory = myHistory afterParsingInputsState ++ actions, lastSonarAction = maybeSonarAction}
  let !out = intercalate "|" (map showOrder (actions ++ [message]))
  send out
  gameLoop precomputed resState

main :: IO ()
main = do
  hSetBuffering stdout NoBuffering -- DO NOT REMOVE
  input_line <- getLine
  let input = words input_line
  let width = read (input !! 0) :: Int
  let height = read (input !! 1) :: Int
  let myid = read (input !! 2) :: Int
  !landMap <- fmap V.fromList (replicateM height $ V.fromList . map (== 'x') <$> getLine)
  startTime <- getCurrentTime
  let allCoords = [Coord x y | x <- [0 .. 14], y <- [0 .. 14]]
  let !waterCoords = filter (isWaterCoord landMap) allCoords :: [Coord]
  let !precomputed = Precomputed {coordsInRange = Map.fromList mapping, waterCoords = waterCoords, landMap = landMap}
        where
          mapping = map (\x -> (x, getTorpedoRange waterCoords landMap x)) waterCoords
          getTorpedoRange waterCoords landMap = bfsLimited torpedoRange waterCoords fn
            where
              fn = map snd . getWaterNeighbors landMap
--  debug (show precomputed)
  let Coord startX startY = findStartCoord waterCoords width height
  endTime <- getCurrentTime
  let elapsed = diffUTCTime endTime startTime
  debug ("spent " ++ show (realToFrac (toRational elapsed * 1000)) ++ " ms")
  send $ show startX ++ " " ++ show startY
  let state =
        State
          {myHistory = [], opponentHistory = [], myCoordHistory = [], lastSonarAction = Nothing, torpedoCooldown = 3, sonarCooldown = 4, silenceCooldown = 6, mineCooldown = 3, myLife = 6, oppLife = 6}
  gameLoop precomputed state
