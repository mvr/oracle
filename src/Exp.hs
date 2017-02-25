module Exp where

import Prelude hiding (not, and, or)
import Control.Applicative (liftA2)
import Control.Monad (replicateM)
import Data.Monoid ((<>))
import Data.List (sortBy, transpose)
import Data.Function (on)
import Test.QuickCheck.Arbitrary
import Test.QuickCheck.Gen

data Action = Cooperate | Defect deriving (Eq, Show)

instance Arbitrary Action where
  arbitrary = do
    b <- arbitrary
    if b then return Cooperate else return Defect

payoff :: (Action, Action) -> (Int, Int)
payoff moves = case moves of
    (Defect, Defect)       -> (1, 1)
    (Defect, Cooperate)    -> (5, 0)
    (Cooperate, Defect)    -> (0, 5)
    (Cooperate, Cooperate) -> (3, 3)

notAction :: Action -> Action
notAction Defect = Cooperate
notAction Cooperate = Defect

andAction :: Action -> Action -> Action
andAction Cooperate Cooperate = Cooperate
andAction _ _ = Defect

data History = History [(Action, Action)] deriving (Eq, Show)

tallyHistory :: History -> (Int, Int)
tallyHistory (History l) = (\(a, b) -> (sum a, sum b)) $ unzip $ fmap payoff l

getSelfHistory :: History -> Int -> Maybe Action
getSelfHistory (History l) i
  | length l < i = Nothing
  | otherwise    = Just $ fst (l !! (i-1))

getOpHistory :: History -> Int -> Maybe Action
getOpHistory (History l) i
  | length l < i = Nothing
  | otherwise    = Just $ snd (l !! (i-1))

swapHistory :: History -> History
swapHistory (History l) = History (map swap l)
  where swap (a, b) = (b, a)

addHistory :: (Action, Action) -> History -> History
addHistory as (History l) = History (as : l)

-- Do I cooperate?
data Agent = Const Action
         | Not Agent
         | And Agent Agent
         | SelfHistory Int Action
         | OpHistory   Int Action
         | Oracle Action
         | SimulateVs Agent
         | Hypothetical Action Action Agent deriving (Eq, Show)

simplifyStep :: Agent -> Agent
simplifyStep (Not (Not e)) = simplifyStep e
simplifyStep (Not (Const Cooperate)) = Const Defect
simplifyStep (Not (Const Defect)) = Const Cooperate
simplifyStep (And (Const Cooperate) e) = simplifyStep e
simplifyStep (And (Const Defect) e) = Const Defect
simplifyStep (And e (Const Cooperate)) = simplifyStep e
simplifyStep (And e (Const Defect)) = Const Defect
simplifyStep (Hypothetical a b (Not e)) = Not (Hypothetical a b e)
simplifyStep (Hypothetical a b (SelfHistory 1 d')) = Const a
simplifyStep (Hypothetical a b (OpHistory 1 d')) = Const b
simplifyStep (Hypothetical a b (SelfHistory n d')) = SelfHistory (n-1) d'
simplifyStep (Hypothetical a b (OpHistory n d')) = SelfHistory (n-1) d'
simplifyStep (Hypothetical _ _ (Const a)) = Const a
simplifyStep (SimulateVs e) = SimulateVs (simplifyStep e)
simplifyStep (Not e) = Not (simplifyStep e)
simplifyStep (And e e') = And (simplifyStep e) (simplifyStep e')
simplifyStep (Hypothetical a b e) = Hypothetical a b (simplifyStep e)
simplifyStep e = e

enumerateAgent :: [Agent]
enumerateAgent = merge $
  [ [Const Cooperate, Const Defect, Oracle Cooperate, Oracle Defect],
    fmap Not enumerateAgent,
    liftA2 And enumerateAgent enumerateAgent,
    fmap (flip SelfHistory Cooperate) [1..],
    fmap (flip SelfHistory Defect) [1..],
    fmap (flip OpHistory Cooperate) [1..],
    fmap (flip OpHistory Defect) [1..],
    fmap (\e -> Hypothetical Cooperate Cooperate e) enumerateAgent,
    fmap (\e -> Hypothetical Cooperate Defect e) enumerateAgent,
    fmap (\e -> Hypothetical Defect Cooperate e) enumerateAgent,
    fmap (\e -> Hypothetical Defect Defect e) enumerateAgent
  ]
  where merge = concat . transpose

simplifyAgent :: Agent -> Agent
simplifyAgent e = let s = simplifyStep e in
                if e == s then e else simplifyAgent s

instance Arbitrary Agent where
  arbitrary = sized $ \n -> do
    let smaller = resize (n - 1) arbitrary
    if n == 0 then do
      k <- choose (1 :: Int, 4)
      case k of
        1 -> Const <$> arbitrary
        2 -> SelfHistory <$> choose (1, 5) <*> arbitrary
        3 -> OpHistory <$> choose (1, 5) <*> arbitrary
        4 -> Oracle <$> arbitrary
        _ -> undefined
    else do
      k <- choose (1 :: Int, 8)
      case k of
        1 -> Const <$> arbitrary
        2 -> SelfHistory <$> choose (1, 5) <*> arbitrary
        3 -> OpHistory <$> choose (1, 5) <*> arbitrary
        4 -> Oracle <$> arbitrary
        5 -> Not <$> smaller
        6 -> And <$> smaller <*> smaller
        7 -> Hypothetical <$> arbitrary <*> arbitrary <*> smaller
        8 -> SimulateVs <$> smaller
        _ -> undefined

and :: Agent -> Agent -> Agent
and = And

not :: Agent -> Agent
not = Not

or :: Agent -> Agent -> Agent
or a b = not (not a `and` not b)

data Env = Env { self :: Agent, opponent :: Agent, history :: History, remainingDepth :: Int }

swapEnv :: Env -> Env
swapEnv (Env s o h r) = Env o s (swapHistory h) r

eval :: Env -> Agent -> Action
eval _ (Const a) = a
eval e (And a b) = andAction (eval e a) (eval e b)
eval e (Not a) = notAction (eval e a)
eval e (SelfHistory n def) = case getSelfHistory (history e) n of
                             Nothing -> def
                             Just h  -> h
eval e (OpHistory n def) = case getOpHistory (history e) n of
                             Nothing -> def
                             Just h  -> h
eval (Env s o h 0) (Oracle def) = def
eval (Env s o h r) (Oracle _) = eval (Env o s (swapHistory h) (r - 1)) o
eval (Env s o h r) (SimulateVs e) = eval (Env o e (swapHistory h) r) o
eval (Env s o h r) (Hypothetical a b e)
  = eval (Env s o (addHistory (a, b) h) r) e

run :: Int -> Int -> Agent -> Agent -> History
run 0 _ _ _ = History []
run n d a b = addHistory (eval (Env a b soFar d) a,
                          eval (Env b a (swapHistory soFar) d) b) soFar
  where soFar = run (n-1) d a b

battle :: Int -> Int -> Agent -> Agent -> (Int, Int)
battle n d a b = tallyHistory (run n d a b)

alwaysCooperate :: Agent
alwaysCooperate = Const Cooperate

alwaysDefect :: Agent
alwaysDefect = Const Defect

titfortat :: Agent
titfortat = OpHistory 1 Cooperate

mirror :: Agent
mirror = Oracle Cooperate

justice :: Agent
justice = Hypothetical Cooperate Cooperate mirror
          `and` Hypothetical Cooperate Defect mirror

karma :: Agent
karma = SimulateVs alwaysCooperate

exploitative :: Agent
exploitative = And (OpHistory 1 Cooperate) (Not (Hypothetical Defect Cooperate (Oracle Defect)))

untrusting :: Agent
untrusting = Hypothetical Cooperate Cooperate (SimulateVs titfortat)

unforgiving :: Agent
unforgiving = And (SelfHistory 1 Cooperate) (OpHistory 1 Cooperate)

standards = [alwaysCooperate, alwaysDefect, mirror, justice, titfortat, karma, exploitative, untrusting, unforgiving]

good1 = SimulateVs (Not (Oracle Defect))
good2 = Hypothetical Cooperate Cooperate (SimulateVs (Not (Oracle Cooperate)))
good3 = SimulateVs (SimulateVs (Const Cooperate))
good4 = SimulateVs (And (Not (Oracle Defect)) (SimulateVs (OpHistory 5 Cooperate)))
good5 = Not (And (Oracle Defect) (Not (SimulateVs (And (Oracle Cooperate) (SimulateVs (Const Defect))))))
good6 = Not (And (SimulateVs (Const Cooperate)) (Oracle Defect))
good7 = Not (And (Oracle Defect) (Hypothetical Cooperate Defect (Oracle Defect)))
good8 = Not (SimulateVs (Not (Hypothetical Defect Cooperate (Oracle Defect))))
good9 = And (Not (Oracle Defect)) (OpHistory 1 Cooperate)
good10 = And (Not (Hypothetical Defect Cooperate (And (Oracle Defect) (Not (SelfHistory 3 Defect))))) (OpHistory 3 Cooperate)
tenlike n = And (Not (Hypothetical Defect Cooperate (And (Oracle Defect) (Not (SelfHistory n Defect))))) (OpHistory n Cooperate)

goods = [good1, good2, good3, good4, good5, good6, good7, good8, good9, good10]


tournament :: Int -> Int -> [Agent] -> [(Agent, Int)]
tournament n d agents = sortBy (compare `on` snd) $ fmap (\a -> (a, totalScore a)) agents
  where totalScore a = sum $ fmap (fst . battle n d a) agents

trial :: Int -> Int -> Int -> [Agent] -> [Agent] -> IO ()
trial n d best done standard = do
  rand <- simplifyAgent <$> (generate $ (resize 15 arbitrary :: Gen Agent))
  if rand `elem` done then
    trial n d best done standard
  else return ()
  let totalScore = sum $ fmap (fst . battle n d rand) standard
  if totalScore >= best then do
    putStrLn $ "Score " <> show totalScore <> ": " <> show rand
    trial n d totalScore (rand:done) standard
  else
    trial n d best (rand:done) standard

search :: Int -> Int -> Int -> [Agent] -> [Agent] -> IO ()
search n d best (rand:rest) standard = do
  let rand' = simplifyAgent rand
  let totalScore = sum $ fmap (fst . battle n d rand') standard
  if totalScore > best then do
    putStrLn $ "Score " <> show totalScore <> ": " <> show rand'
    search n d totalScore rest standard
  else
    search n d best rest standard
