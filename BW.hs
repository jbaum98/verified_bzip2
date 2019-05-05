import Data.List (sortOn, sort)

lrot :: [a] -> [a]
lrot [] = []
lrot xs = tail xs ++ [head xs]

rrot :: [a] -> [a]
rrot [] = []
rrot xs = last xs : init xs

rots :: [a] -> [[a]]
rots xs = take (length xs) $ iterate lrot xs

printMat :: [String] -> IO ()
printMat = mapM_ putStrLn

sortFrom :: Int -> [String] -> [String]
sortFrom 0 m = sortOn (!! i') $ m
    where i' = length m - 1
sortFrom i m = sortOn (!! i') $ sortFrom (i-1) m
    where i' = length m - 1 - i

bwp :: Ord a => [a] -> [a]
bwp = map last . sort . rots

recreate :: Ord a => Int -> [a] -> [[a]]
recreate 0 l = map (const []) l
recreate j l = sortOn head . zipWith (:) l $ recreate (j-1) l

