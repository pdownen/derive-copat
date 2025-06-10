{-# LANGUAGE LambdaCase #-}
module Copattern.Nest.Env.Machine where
import Copattern.Nest.Syntax

data Answer i a
  = Final   (ClosQuestion i a)
  | Stuck   (MetaCont i a) a (ClosQuestion i a)
  | CoStuck (MetaCont i a) a

type MetaCont i a = [Closure i a]

run :: (Eq a, Eq i) => Response i a -> Answer i a
run r = delim r [] []

eval :: (Eq i, Eq a) => Term i a -> Answer i a
eval m = refocus m [] Nop []

try :: (Eq i, Eq a) => Option i a -> Answer i a
try o = comatch o [] Nop (Raise :/: []) Nop []

delim :: (Eq a, Eq i)
         => Response i a -> ClosEnv i a -> MetaCont i a
         -> Answer i a
delim (Splat k) env (m:/:e:s)
  | Just (QSub q) <- lookup k env = refocus m e Nop s
delim (Splat k) env []
  | Just (QSub q) <- lookup k env = Final q
delim (Splat k) env s          = CoStuck s k
delim (End)     env (m:/:e:s)  = refocus m e Nop s
delim (End)     env []         = Final Nop
delim (m :!: r) env s          = delim r env $ (m :/: env) : s

refocus :: (Eq a, Eq i)
     => Term i a -> ClosEnv i a -> ClosQuestion i a -> MetaCont i a
     -> Answer i a
refocus (Var x)    env k s
  | Just (CSub (m:/:e)) <- lookup x env
                               = refocus m e k s
refocus (Var x)    env k s     = Stuck s x k
refocus (Dot m)    env k s     = refocus m env ((m :/: env) :* k) s
refocus (m :*: n)  env k s     = refocus m env ((n :/: env) :* k) s
refocus (m :@: i)  env k s     = refocus m env (i :@ k) s
refocus (Raise)    env k (m:s) = refocus (openTerm m) (staticEnv m) k s
refocus (Raise)    env k []    = Final k
refocus (q :!-> r) env k s     = delim r ((q, QSub k) : env) s
refocus (o :?: m)  env k s     = comatch o env k (m :/: env) k s

comatch :: (Eq i, Eq a)
       => Option i a -> ClosEnv i a -> ClosQuestion i a
       -> Closure i a -> ClosQuestion i a -> MetaCont i a
       -> Answer i a
comatch (x :*-> o) env (n:*k) m q s = comatch o ((x, CSub n) : env) q m k s
comatch (i :@-> o) env (j:@k) m q s
  | i == j                          = comatch o env q m k s
comatch (x :?-> n) env k      m _ s = refocus n ((x, CSub m) : env) k s
comatch _          env _      m q s = refocus (openTerm m) (staticEnv m) q s
