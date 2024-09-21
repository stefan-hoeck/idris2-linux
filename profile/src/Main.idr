module Main

import System.Linux.Pipe
import Profile

%default total

compPrim : Bool -> Nat -> Bool
compPrim b 0     = b
compPrim b (S k) = compPrim (o_direct == o_direct && b) k

compConst : Bool -> Nat -> Bool
compConst b 0     = b
compConst b (S k) = compConst (O_DIRECT == O_DIRECT && b) k

bench : Benchmark Void
bench =
  Group "foreign"
    [ Group "prim call"
        [ Single "1"       (basic (compPrim True) 1)
        , Single "1000"    (basic (compPrim True) 1000)
        , Single "1000000" (basic (compPrim True) 1000000)
        ]
    , Group "constant"
        [ Single "1"       (basic (compConst True) 1)
        , Single "1000"    (basic (compConst True) 1000)
        , Single "1000000" (basic (compConst True) 1000000)
        ]
    ]

main : IO ()
main = do
  runDefault (const True) Table show bench
