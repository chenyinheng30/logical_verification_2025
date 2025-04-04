/- 版权所有 © 2018–2025 Anne Baanen, Alexander Bentkamp, Jasmin Blanchette,
Xavier Généreux, Johannes Hölzl 和 Jannis Limperg。参见 `LICENSE.txt`。 -/

import LoVe.LoVelib


/- # LoVe 演示5：函数式编程

我们将更深入地探讨类型化函数式编程的基础：归纳类型、归纳证明、递归函数、模式匹配、结构体（记录）和类型类。 -/


set_option autoImplicit false
set_option tactic.hygienic false

namespace LoVe


/- ## 归纳类型

回顾 `Nat` 类型的定义： -/

#print Nat

/- 核心原则：

* **无冗余**：该类型不包含无法通过构造函数组合表达的值。

* **无混淆**：通过不同方式构建的值是不同的。

对于 `Nat`：

* "无冗余"意味着不存在特殊值（例如 `–1` 或 `ε`）无法通过有限次组合 `Nat.zero` 和 `Nat.succ` 来表达。

* "无混淆"确保了 `Nat.zero` ≠ `Nat.succ n`。

此外，归纳类型的值总是有限的。`Nat.succ (Nat.succ …)` 不是一个值。


## 结构归纳

__结构归纳__ 是数学归纳法在归纳类型上的推广。要证明所有自然数 `n` 满足性质 `P[n]`，只需证明基本情况

    `P[0]`

和归纳步骤

    `∀k, P[k] → P[k + 1]`

对于列表，基本情况是

    `P[[]]`

归纳步骤是

    `∀y ys, P[ys] → P[y :: ys]`

一般来说，每个构造函数对应一个子目标，并且对于进行归纳的类型的所有构造函数参数，都可以使用归纳假设。 -/

theorem Nat.succ_neq_self (n : ℕ) :
    Nat.succ n ≠ n :=
  by
    induction n with
    | zero       => simp
    | succ n' ih => simp [ih]


/- ## 结构递归

__结构递归__ 是一种递归形式，允许我们从递归值上剥离一个构造函数。这样的函数保证在递归停止前只会有限次调用自身。这是确保函数终止的前提条件。 -/

def fact : ℕ → ℕ
  | 0     => 1
  | n + 1 => (n + 1) * fact n

def factThreeCases : ℕ → ℕ
  | 0     => 1
  | 1     => 1
  | n + 1 => (n + 1) * factThreeCases n

/- 对于结构递归函数，Lean 可以自动证明终止性。对于更一般的递归方案，终止检查可能会失败。有时这是有充分理由的，如下例所示： -/

/-
-- 失败
def illegal : ℕ → ℕ
  | n => illegal n + 1
-/

opaque immoral : ℕ → ℕ

axiom immoral_eq (n : ℕ) :
    immoral n = immoral n + 1

theorem proof_of_False :
    False :=
  have hi : immoral 0 = immoral 0 + 1 :=
    immoral_eq 0
  have him :
    immoral 0 - immoral 0 = immoral 0 + 1 - immoral 0 :=
    by rw [←hi]
  have h0eq1 : 0 = 1 :=
    by simp at him
  show False from
    by simp at h0eq1


/- ## 模式匹配表达式

    `match` _term₁_, …, _termM_ `with`
    | _pattern₁₁_, …, _pattern₁M_ => _result₁_
        ⋮
    | _patternN₁_, …, _patternNM_ => _resultN_

`match` 允许在项内进行非递归模式匹配。 -/

def bcount {α : Type} (p : α → Bool) : List α → ℕ
  | []      => 0
  | x :: xs =>
    match p x with
    | true  => bcount p xs + 1
    | false => bcount p xs

def min (a b : ℕ) : ℕ :=
  if a ≤ b then a else b


/- ## 结构体

Lean 提供了一种便捷的语法来定义记录或结构体。这些本质上是非递归的、单构造函数的归纳类型。 -/

structure RGB where
  red   : ℕ
  green : ℕ
  blue  : ℕ

#check RGB.mk
#check RGB.red
#check RGB.green
#check RGB.blue

namespace RGB_as_inductive

/- RGB 结构体定义等价于以下一组定义： -/

inductive RGB : Type where
  | mk : ℕ → ℕ → ℕ → RGB

def RGB.red : RGB → ℕ
  | RGB.mk r _ _ => r

def RGB.green : RGB → ℕ
  | RGB.mk _ g _ => g

def RGB.blue : RGB → ℕ
  | RGB.mk _ _ b => b

end RGB_as_inductive

/- 可以通过扩展现有结构体来创建新结构体： -/

structure RGBA extends RGB where
  alpha : ℕ

/- 一个 `RGBA` 是一个带有额外字段 `alpha : ℕ` 的 `RGB`。 -/

#print RGBA

def pureRed : RGB :=
  RGB.mk 0xff 0x00 0x00

def pureGreen : RGB :=
  { red   := 0x00
    green := 0xff
    blue  := 0x00 }

def semitransparentGreen : RGBA :=
  { pureGreen with
    alpha := 0x7f }

#print pureRed
#print pureGreen
#print semitransparentGreen

def shuffle (c : RGB) : RGB :=
  { red   := RGB.green c
    green := RGB.blue c
    blue  := RGB.red c }

/- 使用模式匹配的替代定义： -/

def shufflePattern : RGB → RGB
  | RGB.mk r g b => RGB.mk g b r

theorem shuffle_shuffle_shuffle (c : RGB) :
    shuffle (shuffle (shuffle c)) = c :=
  by rfl


/- ## 类型类

__类型类__ 是一种结合了抽象常量及其属性的结构类型。通过为常量提供具体定义并证明属性成立，可以将类型声明为类型类的实例。Lean 根据类型检索相关实例。 -/

#print Inhabited

instance Nat.Inhabited : Inhabited ℕ :=
  { default := 0 }

instance List.Inhabited {α : Type} : Inhabited (List α) :=
  { default := [] }

#eval (Inhabited.default : ℕ)
#eval (Inhabited.default : List Int)

def head {α : Type} [Inhabited α] : List α → α
  | []     => Inhabited.default
  | x :: _ => x

theorem head_head {α : Type} [Inhabited α] (xs : List α) :
    head [head xs] = head xs :=
  by rfl

#eval head ([] : List ℕ)

#check List.head

instance Fun.Inhabited {α β : Type} [Inhabited β] :
  Inhabited (α → β) :=
  { default := fun a : α ↦ Inhabited.default }

instance Prod.Inhabited {α β : Type}
    [Inhabited α] [Inhabited β] :
  Inhabited (α × β) :=
  { default := (Inhabited.default, Inhabited.default) }

/- 我们在第3讲中遇到过这些类型类： -/

#print Std.Associative
#print Std.Commutative


/- ## 列表

`List` 是一个由 `List.nil` 和 `List.cons` 构造的多态归纳类型： -/

#print List

/- `cases` 对指定项进行情况分析。这会根据项类型的构造函数数量产生相应数量的子目标。该策略的行为与 `induction` 相同，只是不产生归纳假设。以下是一个人为示例： -/

theorem head_head_cases {α : Type} [Inhabited α]
      (xs : List α) :
    head [head xs] = head xs :=
  by
    cases xs with
    | nil        => rfl
    | cons x xs' => rfl

/- `match` 是结构化等价物： -/

theorem head_head_match {α : Type} [Inhabited α]
      (xs : List α) :
    head [head xs] = head xs :=
  match xs with
  | List.nil        => by rfl
  | List.cons x xs' => by rfl

/- `cases` 也可以用于形式为 `l = r` 的假设。它将 `r` 与 `l` 匹配，并在目标中用 `r` 中出现的变量替换为 `l` 中对应的项。 -/

theorem injection_example {α : Type} (x y : α) (xs ys : List α)
      (h : x :: xs = y :: ys) :
    x = y ∧ xs = ys :=
  by
    cases h
    simp

/- 如果 `r` 无法匹配 `l`，则不会产生子目标；证明完成。 -/

theorem distinctness_example {α : Type} (y : α) (ys : List α)
      (h : [] = y :: ys) :
    False :=
  by cases h

def map {α β : Type} (f : α → β) : List α → List β
  | []      => []
  | x :: xs => f x :: map f xs

def mapArgs {α β : Type} : (α → β) → List α → List β
  | _, []      => []
  | f, x :: xs => f x :: mapArgs f xs

#check List.map

theorem map_ident {α : Type} (xs : List α) :
    map (fun x ↦ x) xs = xs :=
  by
    induction xs with
    | nil           => rfl
    | cons x xs' ih => simp [map, ih]

theorem map_comp {α β γ : Type} (f : α → β) (g : β → γ)
      (xs : List α) :
    map g (map f xs) = map (fun x ↦ g (f x)) xs :=
  by
    induction xs with
    | nil           => rfl
    | cons x xs' ih => simp [map, ih]

theorem map_append {α β : Type} (f : α → β)
      (xs ys : List α) :
    map f (xs ++ ys) = map f xs ++ map f ys :=
  by
    induction xs with
    | nil           => rfl
    | cons x xs' ih => simp [map, ih]

def tail {α : Type} : List α → List α
  | []      => []
  | _ :: xs => xs

def headOpt {α : Type} : List α → Option α
  | []     => Option.none
  | x :: _ => Option.some x

def headPre {α : Type} : (xs : List α) → xs ≠ [] → α
  | [],     hxs => by simp at *
  | x :: _, hxs => x

#eval headOpt [3, 1, 4]
#eval headPre [3, 1, 4] (by simp)

def zip {α β : Type} : List α → List β → List (α × β)
  | x :: xs, y :: ys => (x, y) :: zip xs ys
  | [],      _       => []
  | _ :: _,  []      => []

#check List.zip

def length {α : Type} : List α → ℕ
  | []      => 0
  | x :: xs => length xs + 1

#check List.length

/- `cases` 也可以与 `Classical.em` 结合使用，对命题进行情况分析。会产生两种情况：一种是命题为真，另一种是命题为假。 -/

#check Classical.em

theorem min_add_add (l m n : ℕ) :
    min (m + l) (n + l) = min m n + l :=
  by
    cases Classical.em (m ≤ n) with
    | inl h => simp [min, h]
    | inr h => simp [min, h]

theorem min_add_add_match (l m n : ℕ) :
    min (m + l) (n + l) = min m n + l :=
  match Classical.em (m ≤ n) with
  | Or.inl h => by simp [min, h]
  | Or.inr h => by simp [min, h]

theorem min_add_add_if (l m n : ℕ) :
    min (m + l) (n + l) = min m n + l :=
  if h : m ≤ n then
    by simp [min, h]
  else
    by simp [min, h]

theorem length_zip {α β : Type} (xs : List α) (ys : List β) :
    length (zip xs ys) = min (length xs) (length ys) :=
  by
    induction xs generalizing ys with
    | nil           => simp [min, length]
    | cons x xs' ih =>
      cases ys with
      | nil        => rfl
      | cons y ys' => simp [zip, length, ih ys', min_add_add]

theorem map_zip {α α' β β' : Type} (f : α → α')
      (g : β → β') :
    ∀xs ys,
      map (fun ab : α × β ↦
          (f (Prod.fst ab), g (Prod.snd ab)))
        (zip xs ys) =
      zip (map f xs) (map g ys)
  | x :: xs, y :: ys => by simp [zip, map, map_zip f g xs ys]
  | [],      _       => by rfl
  | _ :: _,  []      => by rfl


/- ## 二叉树

具有多个递归参数的构造函数的归纳类型定义了树状对象。__二叉树__ 的节点最多有两个子节点。 -/

#print Tree

/- 算术表达式类型 `AExp` 也是树数据结构的一个例子。

树的节点，无论是内部节点还是叶节点，通常带有标签或其他注释。

归纳树不包含无限分支，甚至不包含循环。这比命令式语言中基于指针或引用的数据结构表达能力较弱，但更易于推理。

递归定义（和归纳证明）的工作方式大致与列表相同，但我们可能需要在多个子节点上递归（或调用归纳假设）。 -/

def mirror {α : Type} : Tree α → Tree α
  | Tree.nil        => Tree.nil
  | Tree.node a l r => Tree.node a (mirror r) (mirror l)

theorem mirror_mirror {α : Type} (t : Tree α) :
    mirror (mirror t) = t :=
  by
    induction t with
    | nil                  => rfl
    | node a l r ih_l ih_r => simp [mirror, ih_l, ih_r]

theorem mirror_mirror_calc {α : Type} :
    ∀t : Tree α, mirror (mirror t) = t
  | Tree.nil        => by rfl
  | Tree.node a l r =>
    calc
      mirror (mirror (Tree.node a l r))
      = mirror (Tree.node a (mirror r) (mirror l)) :=
        by rfl
      _ = Tree.node a (mirror (mirror l))
        (mirror (mirror r)) :=
        by rfl
      _ = Tree.node a l (mirror (mirror r)) :=
        by rw [mirror_mirror_calc l]
      _ = Tree.node a l r :=
        by rw [mirror_mirror_calc r]

theorem mirror_Eq_nil_Iff {α : Type} :
    ∀t : Tree α, mirror t = Tree.nil ↔ t = Tree.nil
  | Tree.nil        => by simp [mirror]
  | Tree.node _ _ _ => by simp [mirror]


/- ## 依赖归纳类型（**可选**） -/

inductive Vec (α : Type) : ℕ → Type where
  | nil                                : Vec α 0
  | cons (a : α) {n : ℕ} (v : Vec α n) : Vec α (n + 1)

#check Vec.nil
#check Vec.cons

def listOfVec {α : Type} : ∀{n : ℕ}, Vec α n → List α
  | _, Vec.nil      => []
  | _, Vec.cons a v => a :: listOfVec v

def vecOfList {α : Type} :
    ∀xs : List α, Vec α (List.length xs)
  | []      => Vec.nil
  | x :: xs => Vec.cons x (vecOfList xs)

theorem length_listOfVec {α : Type} :
    ∀(n : ℕ) (v : Vec α n), List.length (listOfVec v) = n
  | _, Vec.nil      => by rfl
  | _, Vec.cons a v =>
    by simp [listOfVec, length_listOfVec _ v]

end LoVe

