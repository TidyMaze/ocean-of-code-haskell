{-# LANGUAGE TupleSections #-}

module Main where

import           Control.Monad
import           Data.List
import qualified Data.Map        as Map
import           Data.Maybe
import           Data.Ord
import           Data.Time.Clock
import           System.IO

data Direction
  = N
  | S
  | W
  | E
  deriving (Read, Enum, Show)

data Power
  = PTorpedo
  | PSonar
  | PSilence
  | PMine
  deriving (Show)

showPower PTorpedo = "TORPEDO"
showPower PSonar   = "SONAR"
showPower PSilence = "SILENCE"
showPower PMine    = "MINE"

type Coord = (Int, Int)

data Order
  = Move Direction (Maybe Power)
  | Torpedo Coord
  | Msg String
  | Surface (Maybe Int)
  | Silence (Maybe (Direction, Int))
  | Sonar (Maybe Int)
  | Mine (Maybe Direction)
  | Trigger Coord

showOrder (Move dir power) = "MOVE " ++ show dir ++ " " ++ maybe "" showPower power
showOrder (Torpedo (x, y)) = "TORPEDO " ++ show x ++ " " ++ show y
showOrder (Msg message) = "MSG " ++ message
showOrder (Surface sector) = "SURFACE " ++ maybe "" show sector
showOrder (Silence dirSize) = "SILENCE " ++ maybe "" (\(d, s) -> show d ++ " " ++ show s) dirSize
showOrder (Sonar sector) = "SONAR " ++ maybe "" show sector
showOrder (Mine dir) = "MINE " ++ maybe "" show dir
showOrder (Trigger (x, y)) = "TRIGGER " ++ show x ++ " " ++ show y

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

parsePower "TORPEDO" = PTorpedo
parsePower "SONAR"   = PSonar
parsePower "SILENCE" = PSilence
parsePower "MINE"    = PMine

isSpace = (== ' ')

trim = dropWhileEnd isSpace . dropWhile isSpace

parseMove rawDir = Move (read rawDir :: Direction) Nothing

parseTorpedo rawX rawY = Torpedo (read rawX :: Int, read rawY :: Int)

parseTrigger rawX rawY = Trigger (read rawX :: Int, read rawY :: Int)

parseSurface rawSector = Surface (Just (read rawSector :: Int))

parseSonar rawSector = Sonar (Just (read rawSector :: Int))

parseOrder o = process (preprocess o)
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

sectorFromCoord (x, y) = y `div` 5 * 3 + x `div` 5 + 1

addDirToCoord (x, y) dir = (x + oX, y + oY)
  where
    (oX, oY) = getOffset dir

getOffset N = (0, -1)
getOffset S = (0, 1)
getOffset W = (-1, 0)
getOffset E = (1, 0)

isInBoard (x, y) = y >= 0 && y < 15 && x >= 0 && x < 15

manhattan (toX, toY) (fromX, fromY) = abs (toX - fromX) + abs (toY - fromY)

diagDst (toX, toY) (fromX, fromY) = (dx + dy) - min dx dy
  where
    dx = abs (fromX - toX)
    dy = abs (fromY - toY)

baryMeanDev :: Fractional a => [Coord] -> Maybe (Coord, a)
baryMeanDev [] = Nothing
baryMeanDev coords = fmap (\b -> (b, fromIntegral (sum (map (diagDst b) coords)) / fromIntegral (length coords))) maybeB
  where
    maybeB = bary coords

bary [] = Nothing
bary coords = Just (avgX, avgY)
  where
    size = length coords
    avgX = sum (map fst coords) `div` size
    avgY = sum (map snd coords) `div` size

isWaterCoord landMap c@(x, y) = isInBoard c && not (landMap !! y !! x)

getPowerToBuy torpedoCooldown sonarCooldown silenceCooldown mineCooldown = maybe PTorpedo fst3 found
  where
    fst3 (a, b, c) = a
    buyList = [(PTorpedo, torpedoCooldown, 3), (PSilence, silenceCooldown, 6), (PSonar, sonarCooldown, 4), (PMine, mineCooldown, 3)]
    found = find (\(power, count, max) -> count > 0) buyList :: Maybe (Power, Int, Int)

allCoords = [(x, y) | x <- [0 .. 14], y <- [0 .. 14]]

findStartCoord :: [Coord] -> Int -> Int -> Coord
findStartCoord waterCoords width height = minimumBy (comparing byManhattanToCenter) waterCoords
  where
    byManhattanToCenter = manhattan (width `div` 2, height `div` 2)

findOpponentPositionFromHistory waterCoords history landMap = map discardAlive (filter isAlive (map (buildPathFrom waterCoords landMap history) allCoords))
  where
    isAlive (_, alive) = alive
    discardAlive (c, alive) = c

buildPathFrom :: Precomputed -> [[Bool]] -> [Order] -> Coord -> (Coord, Bool)
buildPathFrom precomputed landMap history c = foldl execOrder (c, True) history
  where
    execOrder died@(_, False) _ = died
    execOrder (c, true) (Move direction power) = (newC, isWaterCoord landMap newC)
      where
        newC = addDirToCoord c direction
    execOrder (c, true) (Torpedo t) = (c, inTorpedoRange precomputed c t) -- use BFS
    execOrder (c, true) (Surface (Just sector)) = (c, sector == sectorFromCoord c)
    execOrder state otherOrder = state

getWaterNeighbors :: [[Bool]] -> Coord -> [(Direction, Coord)]
getWaterNeighbors landMap c = filter (\(d, dest) -> isWaterCoord landMap dest) neighbors
  where
    computeNeighbor d = (d, addDirToCoord c d)
    neighbors = map computeNeighbor [N, E, S, W]

getUnvisitedWaterNeighborsDir landMap c visited = filter unvisitedWater (getWaterNeighbors landMap c)
  where
    unvisitedWater (d, dest) = dest `notElem` visited

bfs :: [Coord] -> (Coord -> Maybe Int -> [Coord]) -> Coord -> [(Coord, Int)]
bfs waterCoords getNeighbors c = Map.toList (aux initDist initQ)
  where
    initDist = Map.fromList [(c, 0)]
    initQ = waterCoords
    aux :: Map.Map Coord Int -> [Coord] -> Map.Map Coord Int
    aux dist [] = dist
    aux dist q = aux newDist updatedQ
      where
        u = minimumBy (comparing (\x -> fromMaybe 1000 (dist Map.!? x))) q :: Coord
        updatedQ = filter (/= u) q
        newDist = newValues `Map.union` dist
        du = dist Map.!? u
        newValues = Map.fromList (mapMaybe findWhatToUpdate (filter (`elem` q) (getNeighbors u du)))
        maybeAlt = fmap (+ 1) du :: Maybe Int
        findWhatToUpdate v =
          case (maybeAlt, dist Map.!? v) of
            (Just alt, Just old) -> Just (v, min alt old)
            (Nothing, Just old)  -> Nothing
            (Just alt, Nothing)  -> Just (v, alt)
            (Nothing, Nothing)   -> Nothing

bfsLimited :: Int -> [Coord] -> (Coord -> [Coord]) -> Coord -> [(Coord, Int)]
bfsLimited limit waterCoords getNeighbors = bfs waterCoords neighborsWithDist
  where
    neighborsWithDist coord Nothing = []
    neighborsWithDist coord (Just dist) | dist >= 4 = []
    neighborsWithDist coord (Just dist) | dist < 4 = getNeighbors coord

findMove waterCoords landMap c visited opp = listToMaybe (sortOn (\(dir, d) -> criteria opp d) neighbors)
  where
    neighbors = getUnvisitedWaterNeighborsDir landMap c visited
    criteria (Just o) d = (byLonguestPath d, manhattan o d) -- TODO use a bfs to get to target quickly
    criteria Nothing d  = (byLonguestPath d, 0)
    byLonguestPath d =
      if null coordDistances
        then 0
        else -distanceToFarestCoord
      where
        coordDistances = bfs waterCoords fn d
        fn x _ = map snd (getUnvisitedWaterNeighborsDir landMap x visited)
        distanceToFarestCoord = snd (maximumBy (comparing snd) coordDistances)

isSilence (Silence _) = True
isSilence _           = False

cleanOppHistory h =
  if any isSilence h
    then drop 1 (dropWhile (not . isSilence) h)
    else h

minByOption _ [] = Nothing
minByOption f xs = Just (minimumBy (comparing f) xs)

maxDev = 1.5

torpedoRange = 4

getTorpedoRange precomputed from = fromMaybe [] (coordsInRange precomputed Map.!? from)

inTorpedoRange :: Precomputed -> Coord -> Coord -> Bool
inTorpedoRange precomputed from dest = dest `elem` map fst (getTorpedoRange precomputed from)

inExplosionRange center dest = diagDst dest center <= 1

newtype Precomputed =
  Precomputed
    { coordsInRange :: Map.Map Coord [(Coord, Int)]
    }
  deriving (Show)

gameLoop :: Precomputed -> [Coord] -> [[Bool]] -> [Order] -> [Coord] -> IO ()
gameLoop precomputed waterCoords landMap oldOpponentHistory oldMyCoordHistory = do
  input_line <- getLine
  let input = words input_line
  let x = read (input !! 0) :: Int
  let y = read (input !! 1) :: Int
  let mylife = read (input !! 2) :: Int
  let opplife = read (input !! 3) :: Int
  let torpedocooldown = read (input !! 4) :: Int
  let sonarcooldown = read (input !! 5) :: Int
  let silencecooldown = read (input !! 6) :: Int
  let minecooldown = read (input !! 7) :: Int
  input_line <- getLine
  let sonarresult = input_line :: String
  opponentOrders <- getLine
  startTime <- getCurrentTime
  let curCoord = (x, y)
  debug ("third line " ++ opponentOrders)
  let myCoordHistory = oldMyCoordHistory ++ [curCoord]
  let opponentHistory =
        cleanOppHistory
          (if opponentOrders == "NA"
             then oldOpponentHistory
             else oldOpponentHistory ++ parseOrders opponentOrders)
  let opponentCandidates = findOpponentPositionFromHistory precomputed opponentHistory landMap
  debug ("opp candidates (" ++ show (length opponentCandidates) ++ ")")
  let maybeBaryWithMeanDev = baryMeanDev opponentCandidates
  debug ("I think you are at " ++ show maybeBaryWithMeanDev)
  let target = baryFiltered >>= (\(b, meanDev) -> minByOption (Just . manhattan b) waterCoords)
        where
          baryFiltered = mfilter (\(b, dev) -> dev <= maxDev) maybeBaryWithMeanDev
  debug ("Closest waters is " ++ show target)
  let move = findMove waterCoords landMap curCoord myCoordHistory target
  debug ("Move is " ++ show move)
  let (moveAction, endMyCoordHistory, powerBought) =
        case (move, silencecooldown) of
          (Just (d, to), 0) -> (Silence (Just (d, 1)), myCoordHistory, Nothing)
          (Just (d, to), _) -> (Move d (Just powerToBuy), myCoordHistory, Just powerToBuy)
            where powerToBuy = getPowerToBuy torpedocooldown sonarcooldown silencecooldown minecooldown
          (Nothing, _) -> (Surface Nothing, [], Nothing)
  let after = maybe curCoord snd move
  debug ("reachableTarget is " ++ show target)
  let updatedTorpedoCooldown =
        case powerBought of
          Just PTorpedo -> max (torpedocooldown - 1) 0
          _             -> torpedocooldown
  let torpedoAction =
        case (updatedTorpedoCooldown, target) of
          (0, Just rt) -> fmap Torpedo closestToTarget
            where iCanShootSafely c = inTorpedoRange precomputed after c && inExplosionRange c rt && not (inExplosionRange c after) -- use BFS
                  closestToTarget = minByOption (manhattan rt) (filter iCanShootSafely waterCoords)
          (0, Nothing) -> Nothing
          (_, _) -> Nothing
  let message = Msg (show (length opponentCandidates))
  let actions = moveAction : maybeToList torpedoAction ++ [message]
  let out = intercalate "|" (map showOrder actions)
  endTime <- getCurrentTime
  let elapsed = diffUTCTime endTime startTime
  debug ("spent " ++ show (realToFrac (toRational elapsed * 1000)) ++ " ms")
  debug ("out is " ++ out)
  send out
  gameLoop precomputed waterCoords landMap opponentHistory endMyCoordHistory --  debug "start game loop"

main :: IO ()
main = do
  hSetBuffering stdout NoBuffering -- DO NOT REMOVE
  input_line <- getLine
  let input = words input_line
  let width = read (input !! 0) :: Int
  let height = read (input !! 1) :: Int
  let myid = read (input !! 2) :: Int
  landMap <- replicateM height $ map (== 'x') <$> getLine
  let waterCoords = filter (isWaterCoord landMap) allCoords :: [Coord]
  let precomputed = Precomputed (Map.fromList mapping)
        where
          mapping = map (\x -> (x, getTorpedoRange waterCoords landMap x)) waterCoords
          getTorpedoRange waterCoords landMap = bfsLimited torpedoRange waterCoords fn
            where
              fn = map snd . getWaterNeighbors landMap
--  debug (show precomputed)
  let (startX, startY) = findStartCoord waterCoords width height
  send $ show startX ++ " " ++ show startY
  gameLoop precomputed waterCoords landMap [] []
