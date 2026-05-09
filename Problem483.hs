import qualified Data.IntMap.Strict as IM
import Data.Array.Unboxed
import Data.Array.ST
import Control.Monad
import Control.Monad.ST
import Text.Printf
import Data.List (foldl')

n :: Int
n = 350

maxPrimeFactors :: Int -> UArray Int Int
maxPrimeFactors limit = runSTUArray $ do
    arr <- newArray (0, limit) 1 :: ST s (STUArray s Int Int)

    forM_ [2..limit] $ \i -> do
        v <- readArray arr i
        when (v == 1) $ do
            forM_ [i, i + i .. limit] $ \j ->
                writeArray arr j i

    return arr

factorialWeights :: [Double]
factorialWeights =
    scanl (\acc i -> acc / fromIntegral i) 1.0 [1..n]

initialDP :: [IM.IntMap Double]
initialDP =
    [IM.singleton 1 w | w <- factorialWeights]

cycleWeights :: Int -> [(Int, Double)]
cycleWeights c = go 0 1.0
  where
    go t x
        | t > n     = []
        | otherwise = (t, x) : go (t + c) (x / fromIntegral (t + c))

processCycle :: Int -> [IM.IntMap Double] -> [IM.IntMap Double]
processCycle c dp =
    [calc d | d <- [0..n]]
  where
    ws = cycleWeights c

    calc d =
        IM.unionsWith (+)
            [ transform t x (dp !! (d - t))
            | (t, x) <- ws
            , t <= d
            ]

    transform t x mp =
        IM.mapKeysWith (+) newKey $
        IM.map (* x) mp
      where
        newKey k
            | t == 0    = k
            | otherwise = lcm k c

stripPrime :: Int -> [IM.IntMap Double] -> [IM.IntMap Double]
stripPrime p =
    map stripMap
  where
    pp = fromIntegral (p * p)

    stripMap mp =
        IM.fromListWith (+)
            [stripOne k v | (k, v) <- IM.toList mp]

    stripOne k v =
        let (k', v') = remove k v
        in (k', v')

    remove k v
        | k `mod` p == 0 = remove (k `div` p) (v * pp)
        | otherwise      = (k, v)

solve :: Double
solve =
    sum
        [ fromIntegral k * fromIntegral k * v
        | (k, v) <- IM.toList (finalDP !! n)
        ]
  where
    mpf = maxPrimeFactors n

    finalDP =
        foldl' processPrime initialDP [n, n - 1 .. 2]

    processPrime dp p
        | mpf ! p == p =
            let afterCycles =
                    foldl'
                        (\cur c ->
                            if c `mod` p == 0 && mpf ! c == p
                            then processCycle c cur
                            else cur
                        )
                        dp
                        [p, p + p .. n]
            in stripPrime p afterCycles
        | otherwise = dp

formatAnswer :: Double -> String
formatAnswer x =
    let s = printf "%.9e" x :: String
        (mantissa, exponentPart) = break (== 'e') s
    in case exponentPart of
        ('e':'+':rest) -> mantissa ++ "e" ++ normalize rest
        ('e':'-':rest) -> mantissa ++ "e-" ++ normalize rest
        ('e':rest)     -> mantissa ++ "e" ++ normalize rest
        _              -> s
  where
    normalize xs =
        let ys = dropWhile (== '0') xs
        in if null ys then "0" else ys

main :: IO ()
main = putStrLn (formatAnswer solve)
