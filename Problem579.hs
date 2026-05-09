{-# LANGUAGE BangPatterns #-}

import Control.Monad
import Control.Monad.ST
import Data.Array.ST
import Data.Array.Unboxed
import Data.Bits
import Data.Word
import Data.List (foldl')

n :: Int
n = 5000

modulo :: Integer
modulo = 1000000000

tableSize :: Int
tableSize = 1 `shiftL` 23

mask :: Int
mask = tableSize - 1

offset :: Int
offset = 5000

pack3 :: Int -> Int -> Int -> Word64
pack3 a b c =
    fromIntegral (a + offset)
    .|. (fromIntegral (b + offset) `shiftL` 14)
    .|. (fromIntegral (c + offset) `shiftL` 28)

unpack3 :: Word64 -> (Int, Int, Int)
unpack3 x =
    let a = fromIntegral (x .&. 16383) - offset
        b = fromIntegral ((x `shiftR` 14) .&. 16383) - offset
        c = fromIntegral ((x `shiftR` 28) .&. 16383) - offset
    in (a, b, c)

splitmix :: Word64 -> Word64
splitmix x0 =
    let x1 = x0 + 0x9e3779b97f4a7c15
        x2 = (x1 `xor` (x1 `shiftR` 30)) * 0xbf58476d1ce4e5b9
        x3 = (x2 `xor` (x2 `shiftR` 27)) * 0x94d049bb133111eb
    in x3 `xor` (x3 `shiftR` 31)

hashKey :: Word64 -> Word64 -> Word64 -> Int
hashKey a b c =
    fromIntegral (splitmix (a `xor` splitmix b `xor` splitmix c)) .&. mask

gcd3 :: Int -> Int -> Int -> Int
gcd3 a b c = gcd (gcd (abs a) (abs b)) (abs c)

signNormalize :: (Int, Int, Int) -> (Int, Int, Int)
signNormalize v@(x, y, z)
    | x < 0 = neg v
    | x == 0 && y < 0 = neg v
    | x == 0 && y == 0 && z < 0 = neg v
    | otherwise = v
  where
    neg (a, b, c) = (-a, -b, -c)

sort3 :: Ord a => a -> a -> a -> (a, a, a)
sort3 a b c
    | a <= b && b <= c = (a, b, c)
    | a <= c && c <= b = (a, c, b)
    | b <= a && a <= c = (b, a, c)
    | b <= c && c <= a = (b, c, a)
    | c <= a && a <= b = (c, a, b)
    | otherwise        = (c, b, a)

canonicalKey :: Int -> Int -> Int -> Int -> (Word64, Word64, Word64)
canonicalKey a b c d =
    let m00 = a*a + b*b - c*c - d*d
        m01 = 2 * (b*c - a*d)
        m02 = 2 * (b*d + a*c)

        m10 = 2 * (b*c + a*d)
        m11 = a*a - b*b + c*c - d*d
        m12 = 2 * (c*d - a*b)

        m20 = 2 * (b*d - a*c)
        m21 = 2 * (c*d + a*b)
        m22 = a*a - b*b - c*c + d*d

        g = foldl' gcd 0 (map abs [m00,m01,m02,m10,m11,m12,m20,m21,m22])

        c1 = signNormalize (m00 `div` g, m10 `div` g, m20 `div` g)
        c2 = signNormalize (m01 `div` g, m11 `div` g, m21 `div` g)
        c3 = signNormalize (m02 `div` g, m12 `div` g, m22 `div` g)

        ((x1,y1,z1), (x2,y2,z2), (x3,y3,z3)) = sort3 c1 c2 c3
    in
        (pack3 x1 y1 z1 + 1, pack3 x2 y2 z2, pack3 x3 y3 z3)

insertKey
    :: STUArray s Int Word64
    -> STUArray s Int Word64
    -> STUArray s Int Word64
    -> Word64 -> Word64 -> Word64
    -> ST s ()
insertKey arr1 arr2 arr3 k1 k2 k3 = go (hashKey k1 k2 k3)
  where
    go !i = do
        v1 <- readArray arr1 i
        if v1 == 0
            then do
                writeArray arr1 i k1
                writeArray arr2 i k2
                writeArray arr3 i k3
            else if v1 == k1
                then do
                    v2 <- readArray arr2 i
                    v3 <- readArray arr3 i
                    unless (v2 == k2 && v3 == k3) $
                        go ((i + 1) .&. mask)
                else go ((i + 1) .&. mask)

isqrt :: Int -> Int
isqrt x = floor (sqrt (fromIntegral x :: Double))

generateKeys
    :: ST s (STUArray s Int Word64, STUArray s Int Word64, STUArray s Int Word64)
generateKeys = do
    arr1 <- newArray (0, tableSize - 1) 0
    arr2 <- newArray (0, tableSize - 1) 0
    arr3 <- newArray (0, tableSize - 1) 0

    let r = isqrt n

    forM_ [0..r] $ \a -> do
        let a2 = a*a
            bStart = if a == 0 then 0 else -r

        forM_ [bStart..r] $ \b -> do
            let ab2 = a2 + b*b
            when (ab2 <= n) $ do
                let cStart = if a == 0 && b == 0 then 0 else -r

                forM_ [cStart..r] $ \c -> do
                    let abc2 = ab2 + c*c
                    when (abc2 <= n) $ do
                        let rd = isqrt (n - abc2)
                            dStart = if a == 0 && b == 0 && c == 0 then 1 else -rd

                        forM_ [dStart..rd] $ \d -> do
                            let m = abc2 + d*d
                                g = gcd (gcd (abs a) (abs b)) (gcd (abs c) (abs d))

                            when (m > 0 && m <= n && g == 1) $ do
                                let (k1, k2, k3) = canonicalKey a b c d
                                insertKey arr1 arr2 arr3 k1 k2 k3

    return (arr1, arr2, arr3)

cubeData :: Word64 -> Word64 -> Word64 -> (Int, Int, Int, Int, Int)
cubeData k1 k2 k3 =
    let c1@(x1,y1,z1) = unpack3 (k1 - 1)
        c2@(x2,y2,z2) = unpack3 k2
        c3@(x3,y3,z3) = unpack3 k3

        side = isqrt (x1*x1 + y1*y1 + z1*z1)

        sx = abs x1 + abs x2 + abs x3
        sy = abs y1 + abs y2 + abs y3
        sz = abs z1 + abs z2 + abs z3

        gs = colGcd c1 + colGcd c2 + colGcd c3
    in (side, sx, sy, sz, gs)
  where
    colGcd (a,b,c) = gcd3 a b c

contribution :: Int -> Int -> Int -> Int -> Int -> Integer
contribution side sx sy sz gs =
    sum [one t | t <- [1..limit]]
  where
    limit = minimum [n `div` sx, n `div` sy, n `div` sz]

    one t =
        let trans =
                toInteger (n - t*sx + 1)
              * toInteger (n - t*sy + 1)
              * toInteger (n - t*sz + 1)

            td = t * side

            latticePoints =
                toInteger td^3
              + toInteger (t*t*side + t) * toInteger gs
              + 1
        in (trans * latticePoints) `mod` modulo

solve :: Integer
solve = runST $ do
    (arr1, arr2, arr3) <- generateKeys

    total <- foldM step 0 [0..tableSize - 1]
    return (total `mod` modulo)
  where
    step !acc i = do
        k1 <- readArray arr1 i
        if k1 == 0
            then return acc
            else do
                k2 <- readArray arr2 i
                k3 <- readArray arr3 i
                let (side, sx, sy, sz, gs) = cubeData k1 k2 k3
                    add = contribution side sx sy sz gs
                return ((acc + add) `mod` modulo)

main :: IO ()
main = print solve
