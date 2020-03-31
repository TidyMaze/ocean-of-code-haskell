{-# LANGUAGE BangPatterns  #-}
{-# LANGUAGE TupleSections #-}

module Main where

import           Control.Monad
import           Data.List
import qualified Data.Map.Strict as Map
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
  | SonarResult Int Bool
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
    maybeB = fmap (\(bx, by) -> (round bx, round by)) (bary coords)

bary [] = Nothing
bary coords = Just (avgX, avgY)
  where
    size = length coords
    avgX = fromIntegral (sum (map fst coords)) / fromIntegral size
    avgY = fromIntegral (sum (map snd coords)) / fromIntegral size

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

findPositionFromHistory waterCoords history landMap = map discardAlive (filter isAlive (map (buildPathFrom waterCoords landMap cleanedHistory) allCoords))
  where
    cleanedHistory = cleanHistory history
    isAlive (_, alive) = alive
    discardAlive (c, alive) = c

buildPathFrom :: Precomputed -> [[Bool]] -> [Order] -> Coord -> (Coord, Bool)
buildPathFrom precomputed landMap history c = foldl execOrder (c, True) history
  where
    execOrder died@(_, False) _ = died
    execOrder (c, true) (Move direction _) = (newC, isWaterCoord landMap newC)
      where
        newC = addDirToCoord c direction
    execOrder (c, true) (Torpedo t) = (c, inTorpedoRange precomputed c t) -- use BFS
    execOrder (c, true) (Surface (Just sector)) = (c, sector == sectorFromCoord c)
    execOrder (c, true) (SonarResult sector True) = (c, sector == sectorFromCoord c)
    execOrder (c, true) (SonarResult sector False) = (c, sector /= sectorFromCoord c)
    execOrder state otherOrder = state

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
    unvisitedWater (d, dest) = dest `notElem` visited

bfs :: [Coord] -> (Coord -> Maybe Int -> [Coord]) -> Coord -> Map.Map Coord Int
bfs waterCoords getNeighbors c = aux initDist initQ
  where
    initDist = Map.fromList [(c, 0)]
    initQ = waterCoords
    aux :: Map.Map Coord Int -> [Coord] -> Map.Map Coord Int
    aux dist [] = dist
    aux dist q = aux newDist updatedQ
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

findMove waterCoords landMap c visited opp = listToMaybe (sortOn (\(dir, d) -> criteria opp d) neighbors)
  where
    neighbors = getUnvisitedWaterNeighborsDir landMap c visited
    fn x _ = map snd (getUnvisitedWaterNeighborsDir landMap x visited)
    criteria (Just o) d = (byLonguestPath d, fromMaybe 1000 (distancesToO Map.!? d))
      where
        distancesToO = bfs waterCoords fn o
    criteria Nothing d = (byLonguestPath d, 0)
    byLonguestPath d =
      if null coordDistances
        then 0
        else -distanceToFarestCoord
      where
        coordDistances = bfs waterCoords fn d
        distanceToFarestCoord = snd (maximumBy (comparing snd) (Map.toList coordDistances))

isSilence (Silence _) = True
isSilence _           = False

cleanHistory h =
  case splitted of
    [] -> []
    xs -> last xs
  where
    splitted = splitOn isSilence h

minByOption _ [] = Nothing
minByOption f xs = Just (minimumBy (comparing f) xs)

maxDev = 1.5

maxDevDef = 4.5

torpedoRange = 4

getTorpedoRange precomputed from = fromMaybe Map.empty (coordsInRange precomputed Map.!? from)

inTorpedoRange :: Precomputed -> Coord -> Coord -> Bool
inTorpedoRange precomputed from dest = dest `Map.member` getTorpedoRange precomputed from

inExplosionRange center dest = diagDst dest center <= 1

newtype Precomputed =
  Precomputed
    { coordsInRange :: Map.Map Coord (Map.Map Coord Int)
    }
  deriving (Show)

getMoveAction myCoordHistory move torpedocooldown sonarcooldown silencecooldown minecooldown maybeMyBaryWithMeanDev =
  case (move, silencecooldown, maybeMyBaryWithMeanDev) of
    (Just (d, to), 0, Just (b, dev))
      | dev <= maxDevDef -> (Silence (Just (d, 1)), myCoordHistory, Nothing)
    (Just (d, to), _, _) -> (Move d (Just powerToBuy), myCoordHistory, Just powerToBuy)
      where powerToBuy = getPowerToBuy torpedocooldown sonarcooldown silencecooldown minecooldown
    (Nothing, _, _) -> (Surface Nothing, [], Nothing)

getTorpedoAction precomputed waterCoords updatedTorpedoCooldown target after =
  case (updatedTorpedoCooldown, target) of
    (0, Just realTarget) -> fmap Torpedo closestToTarget
      where closestToTarget = minByOption (manhattan realTarget) (filter iCanShootSafely waterCoords)
            iCanShootSafely closeTarget = iCanHitThisCloseCoord && hurtingEnemy && notGettingHurt -- use BFS
              where
                iCanHitThisCloseCoord = inTorpedoRange precomputed after closeTarget
                notGettingHurt = not (inExplosionRange closeTarget after)
                hurtingEnemy = inExplosionRange closeTarget realTarget
    (0, Nothing) -> Nothing
    (_, _) -> Nothing

groupBy :: Ord b => (a -> b) -> [a] -> Map.Map b [a]
groupBy f elems = Map.fromListWith (++) (map (\x -> (f x, [x])) elems)

getSonarAction :: Int -> [Coord] -> Maybe (Coord, Double) -> Maybe Order
getSonarAction cooldown _ _
  | cooldown > 0 = Nothing
getSonarAction _ [] _ = Nothing
getSonarAction _ _ Nothing = Nothing
getSonarAction _ _ (Just (_, dev))
  | dev <= 1.5 = Nothing
getSonarAction _ candidates _ = Just (Sonar (Just (fst biggestSector)))
  where
    biggestSector = maximumBy (comparing (length . snd)) countedCandidatesBySector
    countedCandidatesBySector = Map.assocs (Main.groupBy sectorFromCoord candidates)

parseSonarResult lastSonarAction sonarResult = lastSonarAction >>= parseNew
  where
    parseNew (Sonar (Just sector)) = Just (SonarResult sector (sonarResult == "Y"))
    parseNew _ = Nothing

gameLoop :: Precomputed -> [Coord] -> [[Bool]] -> [Order] -> [Coord] -> [Order] -> Maybe Order -> IO ()
gameLoop !precomputed !waterCoords !landMap !oldOpponentHistory !oldMyCoordHistory !oldMyHistory lastSonarAction = do
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
  let sonarResultAction = parseSonarResult lastSonarAction sonarresult
  let opponentHistory =
        if opponentOrders == "NA"
          then oldOpponentHistory ++ maybeToList sonarResultAction
          else oldOpponentHistory ++ maybeToList sonarResultAction ++ parseOrders opponentOrders
  let !opponentCandidates = findPositionFromHistory precomputed opponentHistory landMap
  let !myCandidates = findPositionFromHistory precomputed oldMyHistory landMap
  debug ("opp candidates (" ++ show (length opponentCandidates) ++ ")")
  debug ("my candidates (" ++ show (length myCandidates) ++ ")")
  let maybeOppBaryWithMeanDev = baryMeanDev opponentCandidates
  let maybeMyBaryWithMeanDev = baryMeanDev myCandidates
  debug ("I think you are at " ++ show maybeOppBaryWithMeanDev)
  debug ("You think I'm at " ++ show maybeMyBaryWithMeanDev)
  let closestWaterTarget = baryFiltered >>= (\(b, meanDev) -> minByOption (manhattan b) waterCoords)
        where
          baryFiltered = mfilter (\(b, dev) -> dev <= maxDev) maybeOppBaryWithMeanDev
  let move = findMove waterCoords landMap curCoord myCoordHistory closestWaterTarget
  debug ("Closest waters is " ++ show closestWaterTarget ++ " and I can get closer with move " ++ show move)
  let (!moveAction, endMyCoordHistory, powerBought) = getMoveAction myCoordHistory move torpedocooldown sonarcooldown silencecooldown minecooldown maybeMyBaryWithMeanDev
  let after = maybe curCoord snd move
  let updatedTorpedoCooldown =
        case powerBought of
          Just PTorpedo -> max (torpedocooldown - 1) 0
          _             -> torpedocooldown
  let !torpedoAction = getTorpedoAction precomputed waterCoords updatedTorpedoCooldown closestWaterTarget after
  let !sonarAction = getSonarAction sonarcooldown opponentCandidates maybeOppBaryWithMeanDev
  endTime <- getCurrentTime
  let elapsed = diffUTCTime endTime startTime
  let spentTime = show (ceiling (realToFrac (toRational elapsed * 1000))) ++ "ms"
  let message = Msg (show (length opponentCandidates) ++ "/" ++ show (length myCandidates) ++ " " ++ spentTime)
  let !actions = moveAction : maybeToList torpedoAction ++ maybeToList sonarAction ++ [message]
  let !myHistory = oldMyHistory ++ actions
  let !out = intercalate "|" (map showOrder actions)
  send out
  gameLoop precomputed waterCoords landMap opponentHistory endMyCoordHistory myHistory sonarAction

main :: IO ()
main = do
  hSetBuffering stdout NoBuffering -- DO NOT REMOVE
  input_line <- getLine
  let input = words input_line
  let width = read (input !! 0) :: Int
  let height = read (input !! 1) :: Int
  let myid = read (input !! 2) :: Int
  !landMap <- replicateM height $ map (== 'x') <$> getLine
  startTime <- getCurrentTime
  let !waterCoords = filter (isWaterCoord landMap) allCoords :: [Coord]
  let !precomputed = Precomputed (Map.fromList mapping)
        where
          mapping = map (\x -> (x, getTorpedoRange waterCoords landMap x)) waterCoords
          getTorpedoRange waterCoords landMap = bfsLimited torpedoRange waterCoords fn
            where
              fn = map snd . getWaterNeighbors landMap
--  debug (show precomputed)
  let (startX, startY) = findStartCoord waterCoords width height
  endTime <- getCurrentTime
  let elapsed = diffUTCTime endTime startTime
  debug ("spent " ++ show (realToFrac (toRational elapsed * 1000)) ++ " ms")
  send $ show startX ++ " " ++ show startY
  gameLoop precomputed waterCoords landMap [] [] [] Nothing
