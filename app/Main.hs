{-# LANGUAGE BangPatterns   #-}
{-# LANGUAGE TupleSections  #-}
{-# OPTIONS_GHC -XStrict #-}
{-# LANGUAGE NamedFieldPuns #-}

module Main where

import           Control.Monad
import           Data.List
import qualified Data.Map.Strict as Map
import           Data.Maybe
import           Data.Ord
import qualified Data.Set        as S
import           Data.Time.Clock
import qualified Data.Vector     as V
import           Debug.Trace     as T
import           System.IO

data Direction
  = N
  | S
  | W
  | E
  deriving (Read, Enum, Show, Eq)

data Power
  = PTorpedo
  | PSonar
  | PSilence
  | PMine
  deriving (Show, Eq)

showPower PTorpedo = "TORPEDO"
showPower PSonar   = "SONAR"
showPower PSilence = "SILENCE"
showPower PMine    = "MINE"

data Coord =
  Coord
    { x :: {-# UNPACK #-}!Int
    , y :: {-# UNPACK #-}!Int
    }
  deriving (Show, Eq, Ord)

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
  deriving (Eq)

instance Show Order where
  show = showOrder

showOrder (Move dir power) = "MOVE " ++ show dir ++ " " ++ maybe "" showPower power
showOrder (Torpedo (Coord x y)) = "TORPEDO " ++ show x ++ " " ++ show y
showOrder (Msg message) = "MSG " ++ message
showOrder (Surface sector) = "SURFACE " ++ maybe "" show sector
showOrder (Silence dirSize) = "SILENCE " ++ maybe "" (\(d, s) -> show d ++ " " ++ show s) dirSize
showOrder (Sonar sector) = "SONAR " ++ maybe "" show sector
showOrder (Mine dir) = "MINE " ++ maybe "" show dir
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

parseOrder :: String -> Order
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

allCoords = [Coord x y | x <- [0 .. 14], y <- [0 .. 14]]

findStartCoord :: [Coord] -> Int -> Int -> Coord
findStartCoord waterCoords width height = minimumBy (comparing byManhattanToCenter) waterCoords
  where
    byManhattanToCenter = manhattan (Coord (width `div` 2) (height `div` 2))

findPositionFromHistory :: Precomputed -> [Order] -> S.Set Coord
findPositionFromHistory !precomputed !history = foldl' (execOrderBulk precomputed) (S.fromList (waterCoords precomputed)) history

execOrderBulk :: Precomputed -> S.Set Coord -> Order -> S.Set Coord
execOrderBulk !precomputed !candidates !action = S.foldl' mergeCoordinates S.empty candidates
  where
    mergeCoordinates acc candidate = S.union acc (execOrder precomputed action candidate)

singleInSetIf :: Bool -> Coord -> S.Set Coord
singleInSetIf !cond coord =
  S.fromList $!
  if cond
    then [coord]
    else []

execOrder :: Precomputed -> Order -> Coord -> S.Set Coord
execOrder precomputed (Move direction _) c = singleInSetIf (isWaterCoord (landMap precomputed) newC) newC
  where
    newC = addDirToCoord c direction
execOrder precomputed (Torpedo t) c = singleInSetIf (inTorpedoRange precomputed c t) c
execOrder _ (Surface (Just sector)) c = singleInSetIf (sector == sectorFromCoord c) c
execOrder _ (SonarResult sector True) c = singleInSetIf (sector == sectorFromCoord c) c
execOrder _ (SonarResult sector False) c = singleInSetIf (sector /= sectorFromCoord c) c
execOrder precomputed (Silence _) c@(Coord cX cY) =
  S.fromList $! filter (\(Coord tx ty) -> (tx == cX && ty /= cY) || (tx /= cX && ty == cY) || (tx == cX && ty == cY)) (Map.keys (fromMaybe Map.empty (coordsInRange precomputed Map.!? c)))
execOrder _ otherOrder state = S.fromList [state]

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
    unvisitedWater (d, dest) = dest `notElem` visited

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
findMove precomputed visited opp = listToMaybe (sortOn (\(dir, d) -> criteria opp d) neighbors)
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

maxDev = 1

maxDevDef = 4

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

getMoveAction :: Precomputed -> State -> Maybe (Coord, Double) -> Maybe Coord -> (Order, [Coord], Int, Int, Coord)
getMoveAction precomputed state maybeMyBaryWithMeanDev maybeClosestWaterTarget = (action, newMyCoordHistory, updatedTorpedoCooldown, updatedSonarCooldown, afterCoord)
  where
    (action, newMyCoordHistory, powerBought) =
      case (maybeMoveWithDest, silenceCooldown state, maybeMyBaryWithMeanDev) of
        (Just (d, to), 0, Just (b, dev))
          | dev <= maxDevDef -> (Silence (Just (d, 1)), myCoordHistory state, Nothing)
        (Just (d, to), _, _) -> (Move d (Just powerToBuy), myCoordHistory state, Just powerToBuy)
          where powerToBuy = getPowerToBuy state
        (Nothing, _, _) -> (Surface Nothing, [], Nothing)
    (updatedTorpedoCooldown, updatedSonarCooldown) =
      case powerBought of
        Just PTorpedo -> (max (torpedoCooldown state - 1) 0, sonarCooldown state)
        Just PSonar -> (torpedoCooldown state, max (sonarCooldown state - 1) 0)
        _ -> (torpedoCooldown state, sonarCooldown state)
    afterCoord = maybe (safeHead "afterCoord" $ myCoordHistory state) snd maybeMoveWithDest
    maybeMoveWithDest = findMove precomputed (myCoordHistory state) maybeClosestWaterTarget

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

getTorpedoAction :: Precomputed -> Int -> Maybe Coord -> Coord -> Bool -> Int -> Int -> Maybe Order
getTorpedoAction precomputed updatedTorpedoCooldown target after oppFound myLife oppLife =
  case (updatedTorpedoCooldown, target, oppFound) of
    (0, Just realTarget, False) -> fmap Torpedo closestToTarget
      where closestToTarget = minByOption (manhattan realTarget) (filter iCanShootSafely (waterCoords precomputed))
            iCanShootSafely closeTarget = iCanHitThisCloseCoord && hurtingEnemy && notGettingHurt
              where
                iCanHitThisCloseCoord = inTorpedoRange precomputed after closeTarget
                notGettingHurt = not (inExplosionRange closeTarget after)
                hurtingEnemy = inExplosionRange closeTarget realTarget
    (0, Just realTarget, True) -> fmap Torpedo closestToTarget
      where closestToTarget =
              fmap
                (\(c, dmgGiven, dmgReceived, diffDmg) -> c)
                (maxByOption (\(c, dmgGiven, dmgReceived, diffDmg) -> (dmgGiven, -dmgReceived)) (filter dontDoAnythingStupid (map getShootData (waterCoords precomputed))))
            dontDoAnythingStupid (c, dmgGiven, dmgReceived, diffDmg) = iCanShootIt && doNotSuicide && iDealDamages && canTakeALotIfIKill
              where
                iCanShootIt = inTorpedoRange precomputed after c
                doNotSuicide = dmgReceived < myLife
                iDealDamages = dmgGiven > 0
                canTakeALotIfIKill = diffDmg > 0 || (dmgGiven >= oppLife && dmgReceived < myLife)
            getShootData c = (c, dmgGiven, dmgReceived, dmgGiven - dmgReceived)
              where
                dmgReceived = explosionDamages c after
                dmgGiven = explosionDamages c realTarget
    (0, Nothing, _) -> Nothing
    (_, _, _) -> Nothing

groupBy :: Ord b => (a -> b) -> [a] -> Map.Map b [a]
groupBy f elems = Map.fromListWith (++) (map (\x -> (f x, [x])) elems)

getSonarAction :: Int -> [Coord] -> Maybe (Coord, Double) -> Maybe Order
getSonarAction cooldown _ _
  | cooldown > 0 = Nothing
getSonarAction _ [] _ = Nothing
getSonarAction _ _ Nothing = Nothing
getSonarAction _ _ (Just (_, dev))
  | dev <= 2 = Nothing
getSonarAction _ candidates _ = Just (Sonar (Just (fst biggestSector)))
  where
    biggestSector = maximumBy (comparing (length . snd)) countedCandidatesBySector
    countedCandidatesBySector = Map.assocs (Main.groupBy sectorFromCoord candidates)

parseSonarResult lastSonarAction sonarResult = lastSonarAction >>= parseNew
  where
    parseNew (Sonar (Just sector)) = Just (SonarResult sector (sonarResult == "Y"))
    parseNew _ = Nothing

buildNewOpponentHistory oldOpponentHistory sonarResultAction "NA" = oldOpponentHistory ++ maybeToList sonarResultAction
buildNewOpponentHistory oldOpponentHistory sonarResultAction opponentOrders = oldOpponentHistory ++ maybeToList sonarResultAction ++ parseOrders opponentOrders

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
    }
  deriving (Show, Eq)

findAttackSequence :: Precomputed -> State -> Maybe Coord -> [([Order], Int)]
findAttackSequence _ _ Nothing = []
findAttackSequence _ state _
  | torpedoCooldown state > 1 = []
findAttackSequence precomputed state (Just target) = findAttackSequenceAfterMove precomputed target (notMoving ++ movingOnce)
  where
    curCoord = safeHead "curCoord3" $ myCoordHistory state
    notMoving = [([], curCoord, torpedoCooldown state)]
    movingOnce = map (\(d, newC) -> ([Move d (Just powerBought)], newC, updatedCD)) neighbors
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

findAttackSequenceAfterMove :: Precomputed -> Coord -> [([Order], Coord, Int)] -> [([Order], Int)]
findAttackSequenceAfterMove precomputed target sequences = concatMap getDmg sequences
  where
    getDmg (orders, curCoord, 0) = map (\c -> (orders ++ [Torpedo c], explosionDamages c target)) (filter ((<= 1) . diagDst target) whereICanShoot) {- - explosionDamages c curCoord -}
      where
        whereICanShoot = Map.keys $ getTorpedoRange precomputed curCoord
    getDmg _ = []

findActionsDeprecated precomputed afterParsingInputsState maybeMyBaryWithMeanDev maybeOppBaryWithMeanDev maybeClosestWaterTarget opponentCandidates oppFound myLife oppLife =
  (moveAction : maybeToList maybeTorpedoAction ++ maybeToList maybeSonarAction, endMyCoordHistory, maybeSonarAction)
  where
    (moveAction, endMyCoordHistory, updatedTorpedoCooldown, updatedSonarCooldown, afterCoord) =
      getMoveAction precomputed afterParsingInputsState maybeMyBaryWithMeanDev (maybeClosestWaterTarget >>= (\(b, meanDev) -> minByOption (manhattan b) (waterCoords precomputed)))
    maybeTorpedoAction = getTorpedoAction precomputed updatedTorpedoCooldown (fmap fst maybeClosestWaterTarget) afterCoord oppFound myLife oppLife
    maybeSonarAction = getSonarAction updatedSonarCooldown opponentCandidates maybeOppBaryWithMeanDev

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
          { myCoordHistory = Coord x y : myCoordHistory oldState
          , opponentHistory = buildNewOpponentHistory (opponentHistory oldState) (parseSonarResult (lastSonarAction oldState) sonarresult) opponentOrders
          , torpedoCooldown = torpedocooldown
          , sonarCooldown = sonarcooldown
          , silenceCooldown = silencecooldown
          , mineCooldown = minecooldown
          }
  debug ("history " ++ show (length $ myHistory afterParsingInputsState) ++ " " ++ show (length $ opponentHistory afterParsingInputsState))
  let !opponentCandidates = S.toList $! findPositionFromHistory precomputed (opponentHistory afterParsingInputsState)
  debug ("opp candidates (" ++ show (length opponentCandidates) ++ "): " ++ show (take 5 opponentCandidates))
  spentTime1 <- getElapsedTime startTime
  debug ("opp: " ++ spentTime1)
  let !myCandidates = S.toList $! findPositionFromHistory precomputed (myHistory afterParsingInputsState)
  debug ("my candidates (" ++ show (length myCandidates) ++ "): " ++ show (take 5 myCandidates))
  spentTime2 <- getElapsedTime startTime
  debug ("me: " ++ spentTime2)
  let maybeOppBaryWithMeanDev = baryMeanDev opponentCandidates
  let oppFound = length opponentCandidates == 1
  let maybeMyBaryWithMeanDev = baryMeanDev myCandidates
  debug ("I think you are at " ++ show maybeOppBaryWithMeanDev)
  debug ("You think I'm at " ++ show maybeMyBaryWithMeanDev)
  let maybeClosestWaterTarget = mfilter (\(b, dev) -> dev <= maxDev) maybeOppBaryWithMeanDev
  debug ("Closest waters is " ++ show maybeClosestWaterTarget)
  let attackSeq =
        sortOn (\(orders, damages) -> (-damages, length orders)) $
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
            where bestSeq = fst . safeHead "bestSeq" $ attackSeq
                  orders = bestSeq ++ maybeToList (fmap (\(action, _, _, _, _) -> action) maybeMoveFallback)
                  maybeMoveFallback =
                    if any isMoveOrSurface bestSeq
                      then Nothing
                      else trace "fallback" (Just (getMoveActionNoTarget precomputed afterParsingInputsState {myCoordHistory = myCoordHistory afterParsingInputsState}))
                  isMoveOrSurface (Move _ _)  = True
                  isMoveOrSurface (Surface _) = True
                  isMoveOrSurface _           = False
                  hist = myCoordHistory afterParsingInputsState
                  maybeSonarAction = Nothing
          [] ->
            trace
              "deprecated"
              findActionsDeprecated
              precomputed
              afterParsingInputsState
              maybeMyBaryWithMeanDev
              maybeOppBaryWithMeanDev
              maybeClosestWaterTarget
              opponentCandidates
              oppFound
              myLife
              oppLife
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
  let state = State {myHistory = [], opponentHistory = [], myCoordHistory = [], lastSonarAction = Nothing, torpedoCooldown = 3, sonarCooldown = 4, silenceCooldown = 6, mineCooldown = 3}
  gameLoop precomputed state
