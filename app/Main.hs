{-# LANGUAGE TupleSections #-}

module Main where

import           Control.Monad
import           Data.List
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

debug :: (Show a) => a -> IO ()
debug = hPrint stderr

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
    buyList = [(PTorpedo, torpedoCooldown, 3), (PSilence, silenceCooldown, 6), (PSonar, sonarCooldown, 4)]
    found = find (\(power, count, max) -> count > 0) buyList :: Maybe (Power, Int, Int)

allCoords = [(x, y) | x <- [0 .. 14], y <- [0 .. 14]]

findStartCoord :: [[Bool]] -> Int -> Int -> Coord
findStartCoord landMap width height = minimumBy (comparing byManhattanToCenter) waterCoords
  where
    byManhattanToCenter = manhattan (width `div` 2, height `div` 2)
    waterCoords = filter (isWaterCoord landMap) allCoords

findOpponentPositionFromHistory history landMap = map discardAlive (filter isAlive (map (buildPathFrom landMap history) allCoords))
  where
    isAlive (_, alive) = alive
    discardAlive (c, alive) = c

buildPathFrom :: [[Bool]] -> [Order] -> Coord -> (Coord, Bool)
buildPathFrom landMap history c = foldl execOrder (c, True) history
  where
    execOrder died@(_, False) _ = died
    execOrder (c, true) (Move direction power) = (newC, isWaterCoord landMap newC)
      where
        newC = addDirToCoord c direction
    execOrder (c, true) (Torpedo t) = (c, manhattan t c <= 4)
    execOrder (c, true) (Surface (Just sector)) = (c, sector == sectorFromCoord c)
    execOrder state otherOrder = state

getUnvisitedWaterNeighborsDir landMap c visited = filter unvisitedWater (map computeNeighbor [N, E, S, W])
  where
    unvisitedWater (d, dest) = isWaterCoord landMap dest && notElem dest visited
    computeNeighbor d = (d, addDirToCoord c d)

bfs :: Coord -> (Coord -> [Coord]) -> [(Coord, Int)]
bfs c getNeighbors = (c, 0) : aux 1 [c] [c]
  where
    aux :: Int -> [Coord] -> [Coord] -> [(Coord, Int)]
    aux _ [] _ = []
    aux depth (x:xs) seen = notVisitedNeighborsWithDist ++ aux (depth + 1) queue newSeen
      where
        notVisitedNeighbors = filter (`notElem` seen) (getNeighbors x)
        notVisitedNeighborsWithDist = map (, depth) notVisitedNeighbors
        queue = xs ++ notVisitedNeighbors
        newSeen = seen ++ notVisitedNeighbors

findMove landMap c visited opp = listToMaybe (sortOn (\(dir, d) -> criteria opp d) neighbors)
  where
    neighbors = getUnvisitedWaterNeighborsDir landMap c visited
    criteria (Just o) d = manhattan o d
    criteria Nothing d = -length (bfs d (\x -> map snd (getUnvisitedWaterNeighborsDir landMap x visited)))

isSilence (Silence _) = True
isSilence _           = False

cleanOppHistory h =
  if any isSilence h
    then drop 1 (dropWhile (not . isSilence) h)
    else h

minByOption _ [] = Nothing
minByOption f xs = Just (minimumBy (comparing f) xs)

oppConsidered = 5

gameLoop :: [[Bool]] -> [Order] -> [Coord] -> IO ()
gameLoop landMap oldOpponentHistory oldMyCoordHistory = do
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
  debug ("before opp " ++ show (map showOrder oldOpponentHistory))
  let opponentHistory =
        cleanOppHistory
          (if opponentOrders == "NA"
             then oldOpponentHistory
             else oldOpponentHistory ++ parseOrders opponentOrders)
  debug ("after opp " ++ show (map showOrder opponentHistory))
  let opponentCandidates =
        if length opponentHistory >= 3
          then findOpponentPositionFromHistory opponentHistory landMap
          else []
  debug ("opp candidates (" ++ show (length opponentCandidates) ++ ") " ++ show opponentCandidates)
  let baryOpp =
        if length opponentCandidates `elem` [1 .. oppConsidered]
          then bary opponentCandidates
          else Nothing
  debug ("I think you are at " ++ show baryOpp)
  let target = baryOpp >>= (\b -> minByOption (Just . manhattan b) waterCoords)
        where
          waterCoords = filter (isWaterCoord landMap) allCoords
  debug ("Closest waters is " ++ show target)
  let move = findMove landMap curCoord myCoordHistory target
  debug ("Move is " ++ show move)
  let (moveAction, endMyCoordHistory) =
        case (move, silencecooldown) of
          (Just (d, to), 0) -> (Silence (Just (d, 1)), myCoordHistory)
          (Just (d, to), _) -> (Move d (Just (getPowerToBuy torpedocooldown sonarcooldown silencecooldown minecooldown)), myCoordHistory)
          (Nothing, _) -> (Surface Nothing, [])
  let after = maybe curCoord snd move
  debug ("reachableTarget is " ++ show target)
  let torpedoAction =
        case (torpedocooldown, target) of
          (0, Just rt) -> fmap Torpedo closestToTarget
            where iCanShootSafely c = isWaterCoord landMap c && manhattan after c <= 4 && diagDst rt c <= 1 && diagDst c after > 1
                  closestToTarget = minByOption (manhattan rt) (filter iCanShootSafely allCoords)
          (0, Nothing) -> Nothing
          (_, _) -> Nothing
  let message = Msg (show (length opponentCandidates))
  let actions = moveAction : maybeToList torpedoAction ++ [message]
  let out = intercalate "|" (map showOrder actions)
  endTime <- getCurrentTime
  let elapsed = diffUTCTime endTime startTime
  debug ("spent " ++ show (realToFrac (toRational elapsed * 1000)) ++ " ms")
  send out
  gameLoop landMap opponentHistory endMyCoordHistory--  debug "start game loop"
--  debug ("fst line " ++ input_line)
--  debug ("snd line " ++ input_line)
main :: IO ()
main = do
  hSetBuffering stdout NoBuffering -- DO NOT REMOVE
  input_line <- getLine
  let input = words input_line
  let width = read (input !! 0) :: Int
  let height = read (input !! 1) :: Int
  let myid = read (input !! 2) :: Int
  landMap <- replicateM height $ map (== 'x') <$> getLine
  debug landMap
  let (startX, startY) = findStartCoord landMap width height
  send $ show startX ++ " " ++ show startY
  gameLoop landMap [] []
