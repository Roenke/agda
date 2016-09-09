module practice1 where

-- 0. flip, const
const : {A B : Set} -> A -> B -> A
const x _ = x

flip : {A B C : Set} -> (A -> B -> C) -> B -> A -> C
flip f fst snd = f snd fst

-- 1. mixfix if_then_else with type polymorphism

data Bool : Set where
  true false : Bool

not : Bool -> Bool
not true = false
not false = true

infix 7 _||_
_||_ : Bool -> Bool -> Bool
true || _ = true
false || x = x

if_then_else_ : {RES : Set} -> Bool -> RES -> RES -> RES
if true then x else _ = x
if false then _ else y = y

-- 2. Определить возведение в степень и факториал для натуральных чисел

data ℕ : Set where
  zero : ℕ
  suc : ℕ → ℕ

infix 5 _+_
_+_ : ℕ → ℕ → ℕ
zero + y = y
suc x + y = suc (x + y)

infix 6 _*_
_*_ : ℕ → ℕ → ℕ
zero * y = zero
suc x * y = y + x * y

fac : ℕ → ℕ
fac zero = suc zero
fac (suc x) = (suc x) * (fac x)

pow : ℕ → ℕ → ℕ
pow value zero = suc zero
pow value (suc degree) = value * pow value degree

-- 3. Определите mod и gcd

_-_ : ℕ → ℕ → ℕ
zero - y = zero
suc x - zero = suc x
suc x - suc y = x - y

_<_ : ℕ → ℕ → Bool
zero < zero = false
zero < suc y = true
suc x < zero = false
suc x < suc y = x < y

div' : ℕ → ℕ → ℕ → ℕ
div' zero x y = zero
div' (suc c) x y = if (x < y) then zero else suc (div' c (x - y) y)

div : ℕ → ℕ → ℕ
div x y = div' x x y

mod' : ℕ → ℕ → ℕ → ℕ
mod' zero a b = a
mod' (suc x) a b = mod' x (a - b) b

mod : ℕ → ℕ → ℕ 
mod a b = mod' (div a b) a b

max : ℕ → ℕ → ℕ
max a b = if a < b then b else a

gcd' : ℕ → ℕ → ℕ → ℕ
gcd' zero a b = a
gcd' _ zero b = b
gcd' _ a zero = a
gcd' (suc x) a b = if b < a then gcd' x (mod a b) b else gcd' x a (mod b a)

gcd : ℕ → ℕ → ℕ
gcd a b = gcd' (max a b) a b

-- 4. Определить (полиморфный) reverse для списков

data List (A : Set) : Set where
  nil : List A
  cons : A → List A → List A

_++_ : {A : Set} → List A → List A → List A
nil ++ ys = ys
cons x xs ++ ys = cons x (xs ++ ys)

reverse : {A : Set} → List A → List A
reverse list = reverse' nil list where
  reverse' : {A : Set} → List A → List A → List A
  reverse' acc nil = acc
  reverse' acc (cons x xs) = reverse' (cons x acc) xs

-- 5. Реализовать любой алгоритм сортировки

length : List ℕ → ℕ
length nil = zero
length (cons x xs) = suc (length xs)

filter : List ℕ → (ℕ → Bool) → List ℕ
filter nil _ = nil
filter (cons x xs) predicate  = if predicate(x)
                           then (cons x (filter xs predicate))
                           else filter xs predicate

sort' : ℕ → List ℕ → List ℕ
sort' zero xs = xs
sort' _ nil = nil
sort' (suc c) (cons x xs)  = ((sort' c lesser) ++ (cons x nil)) ++ (sort' c greater) where
  lesser = filter xs (\p → p < x)
  greater = filter xs (\p → x < p)

sort : List ℕ → List ℕ
sort nil = nil
sort xs = sort' (length xs) xs 


-- 6. Докажите ассоциативность ||

data Unit : Set where
  unit : Unit

data Empty : Set where

absurd : {A : Set} → Empty → A
absurd ()

T : Bool → Set
T true = Unit
T false = Empty

infix 3 _==_
_==_ : Bool → Bool → Bool
true == true = true
true == false = false
false == true = false
false == false = true

||-assoc : (x y z : Bool) → T ((x || y) || z == x || (y || z))
||-assoc true y z = unit
||-assoc false true z = unit
||-assoc false false true = unit
||-assoc false false false = unit

-- 7. Докажите, что fac 3 равен 6 и что fac 2 не равен 3.

infix 3 _=='_
_=='_ : ℕ → ℕ → Bool
zero ==' zero = true
zero ==' suc _ = false
suc _ ==' zero = false
suc x ==' suc y = x ==' y

fac3=6 : T (fac (suc (suc (suc zero))) ==' suc (suc (suc (suc (suc (suc zero))))))
fac3=6 = unit

fac2≠3 : T (fac (suc (suc zero)) ==' suc (suc (suc zero))) → Empty
fac2≠3 = absurd

-- 8. Определите равенство для списков натуральных чисел; докажите, что для любого xs : List ℕ верно, что reverse (reverse xs) равно xs

eq : List ℕ → List ℕ → Bool
eq nil nil = true
eq nil _ = false
eq _ nil = false
eq (cons x xs) (cons y ys) = if x ==' y then eq xs ys else false

testReverse : T (eq (reverse (cons zero (cons (suc(zero)) nil) )) (cons (suc zero) (cons zero nil)))
testReverse = unit

addition : (xs : List ℕ) → (x : ℕ) → T (eq(reverse (cons x xs)) (xs ++ cons x nil))
addition nil zero = unit
addition nil (suc x) = addition nil x
addition (cons x xs) zero = {!!}
addition xs (suc x) = {!!} 

revrev : (xs : List ℕ) → T (eq (reverse (reverse xs)) xs)
revrev nil = unit
revrev (cons zero nil) = unit
revrev (cons zero xs) = ?
revrev (cons (suc x) xs) = ?
