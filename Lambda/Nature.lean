inductive N where
| zero : N
| succ : N -> N
deriving Repr

notation: 9 " zero " => N.zero
notation: 9 " succ " => N.succ
