/- UTLC Lambda Term -/
inductive Term : Type where
-- Quote Define
| Quote(check_name : String) : Term
-- Natural Number
| Zero : Term
| Succ(n : Term) : Term
-- Lambda Calculus
| Abstraction(check_name : String)(rhs_term : Term) : Term
| Application(lambda_term var_term : Term): Term
-- If structure
| If(check_term : Term)(condition : String)
  (true_result : Term)
  (default : Term)
-- Define after eval
| mu : String -> Term -> Term
deriving Repr

-- Syntax Sugar 语法糖
-- Build a string
notation: 9 " ` " x : 10 => toString x
-- Build a Term.Quote
notation: 9 " term " x:10 => (Term.Quote (` x))
-- Term.Zero, Term.Succ
notation: 9 " zero " => (Term.Zero)
notation: 9 " succ " m => (Term.Succ m)

-- Abstraction
notation: 8 "maps" var: 9 " to " content: 9 => Term.Abstraction var content
notation: 8 var " ->> " content => maps var to content

-- Application
notation: 6  " call " fn " at " var => (Term.Application (fn) (var))
notation: 6 lhs:6 " ⬝ " rhs:7 => call lhs at rhs
---- Test 语法糖测试
#eval call term 1 at term 2
#check term 1 ⬝ term 2
-- If
notation: 6 " check " check_term " is " condition " then " true_result " else " default => Term.If check_term condition true_result default
-- Mu
notation: 5 " μ " name: 5 " <> " block_term: 7 => Term.mu name block_term
#eval μ `1 <> term 2

def one := succ zero
def two := succ one

def substitute
: (content : Term) -> (to_sub : String) -> (new_term : Term)
-> Term
:= fun content to_sub new_term =>
  match content with
  | Term.Zero => Term.Zero
  | Term.Succ m => Term.Succ (substitute m to_sub new_term)
  | Term.Quote old_name =>
    if old_name == to_sub
    then new_term
    else content
  | Term.Abstraction var_name result =>
    if var_name == to_sub
    then result
    else maps var_name to substitute result to_sub new_term
  | Term.Application lhs rhs =>
    call (substitute lhs to_sub new_term) at (substitute rhs to_sub new_term)
  | Term.If check_term condition true_term else_term =>
    check check_term is condition
    then
      (if condition == to_sub
      then (substitute true_term to_sub new_term)
      else true_term)
    else else_term
  | Term.mu name block_term =>
    if name == to_sub
    then μ name <> block_term
    else μ name <> (substitute block_term to_sub new_term)

notation: 4 content: 9 " [[ " to_sub: 9 " := " new_term: 9 " ]] "
  => substitute content to_sub new_term

#eval term 1 [[`1 := term 2]]
#check term 1 ⬝ term 2 ⬝ term 3
#eval term 1 ⬝ term 2 ⬝ term 3
#eval μ `1 <> (term 1 [[`1 := term 2]])

/- Reduction to Value -/
-- Value x means x is a Term in our UTLC system
inductive Value : Term -> Type
where
| LambdaValue(x : String)(N : Term): Value (x ->> N)
| ZeroValue : Value Term.Zero
| SuccValue : Value v -> Value (Term.Succ v)




inductive Reduction : Term -> Term -> Type where
| β_Lambda(x : String) (N : Term) (V : Term)
: (Value V)
-> (Reduction ((x ->> N) ⬝ (V)) (N[[x := V]]))

| β_Zero_case (condition : String) (true_result : Term) (else_result : Term)
: Reduction (check Term.Zero is condition then true_resultM else true_result) else_result

| β_Succ_case (x : String) (true_result : Term) (else_result : Term)
: (Value V)
-> Reduction (check Term.Succ V is x then M else N) (N[[x := V]])
| β_mu (x : String) (M : Term)
: Reduction (μ x <> M) (M[[x := (μ x <> M)]])

| η1 (L L' M : Term) : (Reduction L L') -> (Reduction (L ⬝ M) (L' ⬝ M))
| η2 (V M M' : Term) : (Value V) -> (Reduction (V ⬝ M) (V ⬝ M'))
| η_succ(M M' : Term) : (Reduction M M') -> (Reduction (Term.Succ M) (Term.Succ M'))
| η_If (x : String) (L L' : Term) (M N : Term)
: (Reduction L L') -> (Reduction (check L is x then M else N) (check L' is x then M else N))

-- (ƛ "x" ⇒ ` "x") · (ƛ "x" ⇒ ` "x")

#eval (`1 ->> term 1) ⬝ (`1 ->> term 1)



/- Build a simple Type inference system of our UTLC -/


-- Content Inference with simple type
-- T(Type), but the LEAN4 has the keyword Type, here I use T.
inductive T where
| Nat : T
| Map(t1 t2 : T) : T
deriving Repr

-- Here, the content means the sentence of whole code.
-- Every code begins with empty.
-- And we can joind a content with new variable claim. (Genius!)
inductive Content where
| Empty : Content
| Sentence : (Content) -> (x : String) -> (type : T) -> Content
deriving Repr

/- Sugar 语法糖 -/
notation: 9 " ∅ " => Content.Empty
notation: 1 lhs: 1 " ; " mid:2 " is " rhs:3 => Content.Sentence lhs mid rhs

#eval ∅; "x" is T.Nat

-- Look up the given string(variable name) has type A from content.
inductive Lookup: Content -> String -> T -> Type where
| Z(Γ : Content)(x : String)(A : T)
: Lookup Γ x A
| S(Γ : Content)(x y : String)(A B : T)
: (x != y) -> (Lookup Γ x A) -> Lookup (Γ; y is B) x A
/- Lookup Γ x A means: We can lookup x has A type in Γ. -/

notation: 1 content " ∋ " x " is " A => Lookup content x A

-- Type inference
inductive Infer: Content -> Term -> T -> Type where
-- Axiom
| Infer_axiom (Γ : Content)(x : String)(A : T)
: (Γ ∋ x is A)
-> (Infer Γ (Term.Quote x) A)

-- Natural Number
| Infer_zero (Γ : Content)
: Infer Γ Term.Zero T.Nat

| Infer_succ(Γ : Content)(M : Term)
: (Infer Γ M T.Nat)
-> (Infer Γ (Term.Succ M) T.Nat)

-- LC
| Infer_Lambda
: ∀ Γ x N A B,
(Infer (Γ; x is A) N B)
-> (Infer Γ (x ->> N) (T.Map A B))

| Infer_Application(Γ : Content)(M N : Term)(A B : T)
: (Infer Γ M (T.Map A B))
-> (Infer Γ N A)
-> Infer Γ (M ⬝ N) B

| Infer_if
: (Infer Γ L T.Nat)
-> (Infer Γ M A)
-> (Infer (Γ; x is T.Nat) N A)
-> (Infer Γ (check L is x then M else N) A)

| Infer_mu
: (Infer (Γ; x is A) M A)
-> (Infer Γ (μ x <> M) A)

notation: 1 content " ⊢ " x " has " A => Infer content x A
