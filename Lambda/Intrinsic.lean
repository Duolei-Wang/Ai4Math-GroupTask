-- import Lambda.Nature

-- Instrinsic Type
inductive T : Type where
| Nature : T
| Map : T -> T -> T
deriving Repr

notation: 9 " N " => T.Nature
#eval N

notation: 7 lhs " ->> " rhs => T.Map lhs rhs
#eval N ->> N


-- Content
inductive Content : Type where
| Empty : Content
| Joint : Content -> T -> Content
deriving Repr

notation: 9 " φ " => Content.Empty
notation: 5 lhs " , " rhs => Content.Joint lhs rhs
#eval φ
#eval φ, N ->> N

-- Lookup
inductive Lookup : Content -> T -> Type where
| Z(Γ : Content)(A : T) : Lookup (Γ , A) A
| S(Γ : Content)(A B : T)
:(Lookup Γ A)
-> (Lookup (Γ , B) A)

inductive Hastype : Content -> T -> Type where
| zero(Γ : Content) : Hastype Γ T.Nature
-- Build a infer from infer.
| succ(Γ : Content)
: Hastype Γ T.Nature
-> Hastype Γ T.Nature

| fromLookup(Γ : Content)(A : T)
: (Lookup Γ A)
-> Hastype Γ A

| application (Γ : Content) (A B : T)
: Hastype Γ (A ->> B)
-> (Hastype Γ A)
-> Hastype Γ B

| abstraction (Γ : Content) (A B : T)
: Hastype (Γ, A) B
-> Hastype Γ (A ->> B)

| case (Γ : Content) (A : T)
: Hastype Γ T.Nature
-> Hastype Γ A
-> Hastype (Γ, T.Nature) A
-> Hastype Γ A

| mu (Γ : Content) (A : T)
: Hastype (Γ , A) A
-> Hastype Γ A

def rename(Γ Δ : Content)
