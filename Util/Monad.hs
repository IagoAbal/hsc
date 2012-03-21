
module Util.Monad where


mapAccumM :: Monad m => (acc -> x -> m (y,acc)) -> acc -> [x] -> m ([y], acc)
mapAccumM _ acc []     = return ([],acc)
mapAccumM f acc (x:xs) = do (y,acc') <- f acc x
                            (ys,acc'') <- mapAccumM f acc' xs
                            return (y:ys,acc'')


andM :: Monad m => m [Bool] -> m Bool
andM = (>>= return . and)
