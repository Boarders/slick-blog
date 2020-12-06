---
title: "Advent of Code 2020 (Days 1-3)"
author: Callan McGill
date: "Dec 3, 2020"
tags: [Haskell, Advent of Code]
description: Haskell soltuions to Advent Of Code days  1 to 3.
quote: I will honor Christmas in my heart, and try to keep it all the year.
quoteAuthor: Charles Dickens

---

The capacity for humans to suffuse ritual with new meaning is one of life's great joys.
Advent of Code is one such ritual pleasure for me -- something that has, in its 5 short years, brightened my holiday season more 
than any Christmas bauble ever could (though you did try, Rockefeller tree!). I began participating in this particular coding-based ritual around the time that I was giving both programming and Haskell
a serious go; this was shortly after unhappily leaving a PhD program that didn't quite fit. Advent of Code played no small
part in both salving my then beleaguered soul and getting to grips with
the nuts and bolts that make up so much of what we do as programmers. I would be remiss if I didn't 
point out that Advent of Code has redefined my holiday rituals in the best way possible. For this gift I am forever thankful to Advent of Code's creator Eric Wastl.

I like each year to both aim to get as far as I can through Advent of Code's 25 puzzles, but also to try to have some wider focus.
One year I may take the opportunity to see how far I can get in a new language, another to see
how elegant the code I write can be. This year I decided I wanted to concentrate on some mix of
Haskell's algorithmic elegance with reasonably good performance in mind. Here's how that turned out
the first three days:

Day 1
-----

Day 1 gave us input consisting of a list of integers as so:
```terminal
1721
979
366
299
675
1456
```
In the first puzzle, we were to find the product of the (unique) two integers in the
list that sum to 2020. The second called for the product of the three (unqiue) integers that sum to 2020.
In general, it is good practice to separate out the proessing of
input (parsing) from the algorithm itself. Since we had such constrained input, we stuck with
only using a `ByteString` to read the input. Therefore, our parsing step was as follows:

```haskell
import qualified Data.ByteString.Char8 as ByteString

parseInput :: IO [Int]
parseInput = do
  bs <- ByteString.readFile "input/day1.dat"  
  pure 
    . fmap (fst . fromJust . ByteString.readInt) 
    . ByteString.lines 
    $ bs
```
Here we made use of the `readInt` function of type
`readInt :: ByteString -> Maybe (Int, ByteString)` and we used an unsafe `fromJust`
since the input consisted of only integers.

I originally started with
the elegant but naive quadratic and cubic solutions making use of list comprehensions:
```haskell
sum_2020 :: [Int] -> Int
sum_2020 xs =
  head [ x * y | x <- xs, y <- tail xs, x + y == 2020]


sum3_2020 :: [Int] -> Int
sum3_2020 xs =
  head [ x * y * z 
       | x <- xs, y <- tail xs
       , z <- tail (tail xs)
       , x + y + z == 2020
       ]
```

We could then measure how this performed using criterion as follows:
```haskell
module Main where

import qualified Criterion.Main  as Criterion
  (bench, bgroup, defaultMain, env, nf)
import qualified Day1 as Day1

main :: IO ()
main = do
  Criterion.defaultMain . pure $
    Criterion.bgroup "advent of code"
    [ Criterion.env Day1.parseInput $ \ ~d1 ->
         Criterion.bgroup "day1"
        [ Criterion.bench "sol1" $ 
            Criterion.nf Day1.sum_2020  d1
        , Criterion.bench "sol2" $ 
            Criterion.nf Day1.sum3_2020 d1
        ]
    ]
```
Here we used Criterion's `env` function which allowed us to separate out the time
spent parsing from the algorithms themselves. The performance of the first
solution (on such a small input) was quite reasonable but
the cubic performance starts to sting for problem 2:

```terminal
benchmarking advent of code/day1/sol1
time                 14.96 μs   (14.87 μs .. 15.06 μs)
                     1.000 R²   (1.000 R² .. 1.000 R²)
mean                 14.96 μs   (14.90 μs .. 15.04 μs)
std dev              227.6 ns   (185.3 ns .. 288.1 ns)
variance introduced by outliers: 12% (moderately inflated)

benchmarking advent of code/day1/sol2
time                 7.146 ms   (7.075 ms .. 7.198 ms)
                     0.999 R²   (0.999 R² .. 1.000 R²)
mean                 7.137 ms   (7.091 ms .. 7.192 ms)
std dev              145.2 μs   (110.9 μs .. 213.8 μs)
```

After some more thought, I realised that we could build an `IntSet` of the entries
and then find the first that is the complement of 2020 in each case:

```haskell
s1 :: [Int] -> Int
s1 xs = 
    head [ x * (2020 - x) 
         | x <- xs, (2020 - x) `IntSet.member` ints
         ]
  where
    ints :: IntSet.IntSet
    ints = IntSet.fromList xs

s2 :: [Int] -> Int
s2 xs = 
    head [ x * y * (2020 - x - y) 
         | x <- xs
         , y <- tail xs
         , (2020 - x - y) `IntSet.member` ints
         ]
  where
    ints :: IntSet.IntSet
    ints = IntSet.fromList xs
```

The performance here was quite a bit better:
```terminal
benchmarking advent of code/day1/sol1
time                 6.033 μs   (5.961 μs .. 6.144 μs)
                     0.998 R²   (0.995 R² .. 0.999 R²)
mean                 6.070 μs   (5.996 μs .. 6.209 μs)
std dev              301.0 ns   (198.5 ns .. 466.5 ns)
variance introduced by outliers: 61% (severely inflated)

benchmarking advent of code/day1/sol2
time                 86.29 μs   (85.34 μs .. 87.68 μs)
                     0.999 R²   (0.998 R² .. 0.999 R²)
mean                 86.13 μs   (85.36 μs .. 87.13 μs)
std dev              3.090 μs   (2.620 μs .. 3.636 μs)
variance introduced by outliers: 36% (moderately inflated)
```
At this point there were probably various further improvements we could haved tried, 
but in the spirit of the season, I grabbed myself a Kinder Surprise and decided that this was a satisfactory place for me to leave things.

Day 2
-----

This challenge gave us input data as follows:
```terminal
1-3 a: abcde
1-3 b: cdefg
2-9 c: ccccccccc
```
Here we were to read `1-3 a` as a password policy. The text following the colon can then be read as
the given password. Our task was to count the number of passwords from the input that
meet the  given policy. The first puzzle's policy, read as `1-3 a`, states that the password contains 
between one and three a's (inclusive). In the second puzzles's policy, we read the same piece of 
text, `1-3 a`, to demand that either of the letters at password positions one or three is an 'a', but not both.

In order to get the input, we used `attoparsec` to parse the policy and password:
```haskell
import Data.Attoparsec.ByteString.Char8

data Range = Range
  { low  :: !Int
  , high :: !Int
  }

data PassInfo = PassInfo
  { passRange :: !Range
  , target    :: !Char
  , password  :: !ByteString
  }

parsePassInfo :: Parser PassInfo
parsePassInfo = do
  l <- decimal
  void $ char '-'
  h <- decimal
  void $ space
  tgt <- anyChar
  void $ char ':'
  void $ space
  pass <- takeByteString
  pure (PassInfo (Range l h) tgt pass)

parseInput :: IO (Either String [PassInfo])
parseInput = do
  bs <- ByteString.readFile "input/day2.dat"
  let
    input = 
      traverse (parseOnly parsePassInfo) (ByteString.lines bs)
  pure input
```

For the first part we define a function to count the occurences of a letter
using `foldl'` from `Data.ByteString.Char8`:
```haskell
countLetter :: ByteString -> Char -> Int
countLetter bs tgt = ByteString.foldl occurs 0 bs
  where
    occurs :: Int -> Char -> Int
    occurs acc c | c == tgt  = acc + 1
                 | otherwise = acc
```

We can then count the number of valid passwords as follows:
```haskell
valid1 :: PassInfo -> Bool
valid1 (PassInfo (Range l h) tgt pass) =
  let c = countLetter pass tgt in
    (l <= c && c <= h)

s1 :: Either String [PassInfo] -> Either String Int
s1 = fmap (length . filter valid1)
```

Part 2 is much the same, only we just need to check the letter only occurs once:
```haskell
occursOnce :: ByteString -> Range -> Char -> Bool
occursOnce bs (Range l' h') c =
  bs `ByteString.index` l == c && bs `ByteString.index` h /= c ||
  bs `ByteString.index` l /= c && bs `ByteString.index` h == c
  where
 -- go from 1 to 0-indexing 
    l = l' - 1
    h = h' - 1

valid2 :: PassInfo -> Bool
valid2 (PassInfo range tgt pass) = occursOnce pass range tgt

s2 :: Either String [PassInfo] -> Either String Int
s2 = fmap (length . filter valid2)
```

The performance in both cases here was quite reasonble without further effort and
so I didn't put more time into experimenting with any tweaks here (off for another Kinder sweet):
```terminal
benchmarking advent of code/day2/sol1
time                 62.30 μs   (61.10 μs .. 63.93 μs)
                     0.996 R²   (0.992 R² .. 0.999 R²)
mean                 63.08 μs   (62.21 μs .. 64.70 μs)
std dev              3.788 μs   (2.581 μs .. 6.136 μs)
variance introduced by outliers: 63% (severely inflated)

benchmarking advent of code/day2/sol2
time                 9.889 μs   (9.668 μs .. 10.11 μs)
                     0.996 R²   (0.993 R² .. 0.998 R²)
mean                 10.07 μs   (9.874 μs .. 10.41 μs)
std dev              887.2 ns   (435.9 ns .. 1.405 μs)
variance introduced by outliers: 83% (severely inflated)
```

Day 3
-----

Day 3 presented us with an ascii map as input:
```terminal
..##.......
#...#...#..
.#....#..#.
..#.#...#.#
.#...##..#.
..#.##.....
.#.#.#....#
.#........#
#.##...#...
#...##....#
.#..#...#.#
```
We were to view the map as cylindrical in the sense that,
as we take any step off the map to the right, we would wind up back
on the lefthand side. In the first puzzle we were tasked with
traversing the map from top to bottom with each step going one down 
and three to the right. This started from the top left square.
As we did this,  we counted the number of '#'s we encountered.

We parsed the input by splitting it into lines which we could then fold over:

```haskell
parseInput :: IO [ByteString]
parseInput = do
  bs <- ByteString.readFile "input/day3.dat"
  pure $ ByteString.lines bs
```

The main difficulty here was figuring out the index on a cylindrical map. We
created a custom data type for the map's row length and the size of the step
we were taking:

```haskell
data Step = Step
  { rowLenS :: !Int
  , stepS   :: !Int
  }
```

We then find the cylindrical index as follows:
```haskell
findInd :: Step -> Int -> Int
findInd (Step rowLen step) row =
  row * step `mod` rowLen
```

Since we were on a cylindrical map, we needed to take the product of the row 
and the stride length modulo the row length. We could then count the '#''s we see:
```haskell
countTrees :: Int -> [ByteString] -> Int
countTrees step bss =
    snd . foldl' c (0, 0) $ bss
  where
    rowLen = ByteString.length . head $ bss
    st = Step rowLen step
    
    c :: (Int, Int) -> ByteString -> (Int, Int)
    c (row, count) bs =
       ( row + 1
       , count + fromEnum (bs `index` findInd st row == '#')
       )

s1 :: [ByteString] -> Int
s1 = countTrees 3
```
Here we again used `foldl'` (this time over lists) and added to
the count if the character at the cylindrical index was a '#'.


For the second part, we were asked to do the same task only this time using: paths
going down 1 and to the right 1, 3, 5 and 7 respectively; and a path going down 2 and
along 1. Since my fold wasn't well equipped for skipping between rows,
I decided to hackily copy and paste what I already had for the last case:
```haskell
countTrees2 :: Int -> [ByteString] -> Int
countTrees2 step bss = 
    (\(_,_,cnt) -> cnt) . foldl' c (True, 0, 0) $ bss
  where
    rowLen = ByteString.length . head $ bss
    st = Step rowLen step
    
    c :: (Bool, Int, Int) -> ByteString -> (Bool, Int, Int)
    c (alt, jump, count) bs =
      if alt
        then
          ( not alt
          , jump + 1 
          , count + fromEnum (bs `index` findInd st jump == '#')
          )
        else
          (not alt, jump, count)
```
In the accumulator we kept track of a boolean which we alternated for those rows
we wished to count versus those we were skipping. The second puzzle then asked us to
multiply all of these together which we did as follows:
```haskell
s2 :: [ByteString] -> Int
s2 input =
    (product . map (\i -> countTrees i input) $ [1,3,5,7]) 
  * countTrees2 1 input
```

The performance here was also reasonable on the first try, and so again
I didn't put any further efforts into doing better, this time trading my keyboard for two Kinder bonbons:
```terminal

benchmarking advent of code/day3/sol1
time                 5.614 μs   (5.585 μs .. 5.647 μs)
                     1.000 R²   (1.000 R² .. 1.000 R²)
mean                 5.660 μs   (5.623 μs .. 5.700 μs)
std dev              130.4 ns   (102.9 ns .. 173.3 ns)
variance introduced by outliers: 26% (moderately inflated)

benchmarking advent of code/day3/sol2
time                 24.18 μs   (23.99 μs .. 24.36 μs)
                     1.000 R²   (1.000 R² .. 1.000 R²)
mean                 24.17 μs   (24.07 μs .. 24.30 μs)
std dev              374.4 ns   (304.0 ns .. 496.4 ns)
variance introduced by outliers: 12% (moderately inflated)
```

Thank you for reading! The full code for this post is available
[here](https://github.com/Boarders/advent-of-code/tree/master/2020). Please
feel free to contact me
[here](mailto:callan.mcgill@gmail.com) with questions, thoughts, ideas, or all of the above.


<i>With warmest thanks to Alixandra Prybyla for their valuable feedback.</i>
