-- UTLC
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
notation: 9 " ` " x:10 => toString x
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

/- Reduction -/
/- What is Value? -/
inductive Value : Term -> Type
where
| VLambda(x : String)(N : Term): Value (maps x to N)
| VZero : Value Term.Zero
| VSucc : Value v -> Value (Term.Succ v)
