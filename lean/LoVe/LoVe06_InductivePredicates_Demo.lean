/- 版权声明 © 2018–2025 Anne Baanen, Alexander Bentkamp, Jasmin Blanchette,
Xavier Généreux, Johannes Hölzl 和 Jannis Limperg。参见 `LICENSE.txt` 文件。 -/

import LoVe.LoVe04_ForwardProofs_Demo
import LoVe.LoVe05_FunctionalProgramming_Demo


/- # LoVe 演示6：归纳谓词

__归纳谓词__，或称归纳定义的命题，是定义类型为`⋯ → Prop`的函数的便捷方式。它们让人联想到形式系统和逻辑编程语言Prolog的Horn子句。

对Lean的一种可能看法：

    Lean = 函数式编程 + 逻辑编程 + 更多逻辑 -/


set_option autoImplicit false
set_option tactic.hygienic false

namespace LoVe


/- ## 入门示例

### 偶数

数学家常将集合定义为满足某些条件的最小集合。例如：

    自然数偶数集`E`定义为满足以下规则的最小集合：(1) `0 ∈ E`；(2) 对于每个`k ∈ ℕ`，如果`k ∈ E`，则`k + 2 ∈ E`。

在Lean中，我们可以如下定义对应的"是偶数"谓词： -/

inductive Even : ℕ → Prop where
  | zero    : Even 0
  | add_two : ∀k : ℕ, Even k → Even (k + 2)

/- 这看起来应该很熟悉。我们使用了相同的语法，只是用`Prop`代替了`Type`来定义归纳类型。

上述命令引入了一个新的一元谓词`Even`以及两个构造子`Even.zero`和`Even.add_two`，可用于构建证明项。得益于归纳定义的"无冗余"保证，`Even.zero`和`Even.add_two`是构造`Even`证明的唯二方式。

根据PAT原则，`Even`可被视为归纳类型，其值即为证明项。 -/

theorem Even_4 :
    Even 4 :=
  have Even_0 : Even 0 :=
    Even.zero
  have Even_2 : Even 2 :=
    Even.add_two _ Even_0
  show Even 4 from
    Even.add_two _ Even_2

/- 为什么我们不能简单地递归定义`Even`呢？确实，为何不可？ -/

def evenRec : ℕ → Bool
  | 0     => true
  | 1     => false
  | k + 2 => evenRec k

/- 两种风格各有优缺点。

递归版本需要我们指定假情况(1)，且需要考虑终止性。但正因其可计算，它能很好地与`rfl`、`simp`、`#reduce`和`#eval`配合使用。

归纳版本通常被认为更抽象优雅。每条规则都独立于其他规则陈述。

定义`Even`的另一种方式是非递归定义： -/

def evenNonrec (k : ℕ) : Prop :=
  k % 2 = 0

/- 数学家可能认为这是最令人满意的定义。但归纳版本是一个方便直观的典型示例，体现了许多现实中的归纳定义。


### 网球比赛

转移系统由转移规则组成，共同指定连接"前"状态和"后"状态的二元谓词。作为转移系统的简单示例，我们考虑网球比赛中从0–0开始的可能转移。 -/

inductive Score : Type where
  | vs       : ℕ → ℕ → Score
  | advServ  : Score
  | advRecv  : Score
  | gameServ : Score
  | gameRecv : Score

infixr:50 " – " => Score.vs

inductive Step : Score → Score → Prop where
  | serv_0_15     : ∀n, Step (0–n) (15–n)
  | serv_15_30    : ∀n, Step (15–n) (30–n)
  | serv_30_40    : ∀n, Step (30–n) (40–n)
  | serv_40_game  : ∀n, n < 40 → Step (40–n) Score.gameServ
  | serv_40_adv   : Step (40–40) Score.advServ
  | serv_adv_40   : Step Score.advServ (40–40)
  | serv_adv_game : Step Score.advServ Score.gameServ
  | recv_0_15     : ∀n, Step (n–0) (n–15)
  | recv_15_30    : ∀n, Step (n–15) (n–30)
  | recv_30_40    : ∀n, Step (n–30) (n–40)
  | recv_40_game  : ∀n, n < 40 → Step (n–40) Score.gameRecv
  | recv_40_adv   : Step (40–40) Score.advRecv
  | recv_adv_40   : Step Score.advRecv (40–40)
  | recv_adv_game : Step Score.advRecv Score.gameRecv

infixr:45 " ↝ " => Step

/- 注意虽然`Score.vs`允许任意数字作为参数，但`Step`构造子的表述确保只有有效的网球比分能从`0–0`达到。

我们可以提出并正式回答诸如：比分能否回到`0–0`？ -/

theorem no_Step_to_0_0 (s : Score) :
    ¬ s ↝ 0–0 :=
  by
    intro h
    cases h


/- ### 自反传递闭包

我们的最后一个入门示例是关系`R`的自反传递闭包，建模为二元谓词`Star R`。 -/

inductive Star {α : Type} (R : α → α → Prop) : α → α → Prop
where
  | base (a b : α)    : R a b → Star R a b
  | refl (a : α)      : Star R a a
  | trans (a b c : α) : Star R a b → Star R b c → Star R a c

/- 第一条规则将`R`嵌入`Star R`。第二条规则实现自反闭包。第三条规则实现传递闭包。

这个定义非常优雅。若存疑，可尝试将`Star`实现为递归函数： -/

def starRec {α : Type} (R : α → α → Bool) :
  α → α → Bool :=
  sorry


/- ### 非法示例

并非所有归纳定义都是合法的。 -/

/-
-- 失败
inductive Illegal : Prop where
  | intro : ¬ Illegal → Illegal
-/


/- ## 逻辑符号

真值`False`和`True`，连接词`∧`、`∨`和`↔`，存在量词`∃`，以及相等谓词`=`都定义为归纳命题或谓词。相比之下，`∀`和`→`是逻辑内置的。

语法糖：

    `∃x : α, P` := `Exists (λx : α, P)`
    `x = y`     := `Eq x y` -/

namespace logical_symbols

inductive And (a b : Prop) : Prop where
  | intro : a → b → And a b

inductive Or (a b : Prop) : Prop where
  | inl : a → Or a b
  | inr : b → Or a b

inductive Iff (a b : Prop) : Prop where
  | intro : (a → b) → (b → a) → Iff a b

inductive Exists {α : Type} (P : α → Prop) : Prop where
  | intro : ∀a : α, P a → Exists P

inductive True : Prop where
  | intro : True

inductive False : Prop where

inductive Eq {α : Type} : α → α → Prop where
  | refl : ∀a : α, Eq a a

end logical_symbols

#print And
#print Or
#print Iff
#print Exists
#print True
#print False
#print Eq


/- ## 规则归纳

正如我们可以对项进行归纳，我们也可以对证明项进行归纳。

这称为__规则归纳__，因为归纳是基于引入规则(即证明项的构造子)。得益于PAT原则，这能如预期工作。 -/

theorem mod_two_Eq_zero_of_Even (n : ℕ) (h : Even n) :
    n % 2 = 0 :=
  by
    induction h with
    | zero            => rfl
    | add_two k hk ih => simp [ih]

theorem Not_Even_two_mul_add_one (m n : ℕ)
      (hm : m = 2 * n + 1) :
    ¬ Even m :=
  by
    intro h
    induction h generalizing n with
    | zero            => linarith
    | add_two k hk ih =>
      apply ih (n - 1)
      cases n with
      | zero    => simp [Nat.ctor_eq_zero] at *
      | succ n' =>
        simp [Nat.succ_eq_add_one] at *
        linarith

/- `linarith`证明涉及线性算术等式或不等式的目标。"线性"意味着它仅处理`+`和`-`，而非`*`和`/`(但支持乘以常数)。 -/

theorem linarith_example (i : Int) (hi : i > 5) :
    2 * i + 3 > 11 :=
  by linarith

theorem Star_Star_Iff_Star {α : Type} (R : α → α → Prop)
      (a b : α) :
    Star (Star R) a b ↔ Star R a b :=
  by
    apply Iff.intro
    { intro h
      induction h with
      | base a b hab                  => exact hab
      | refl a                        => apply Star.refl
      | trans a b c hab hbc ihab ihbc =>
        apply Star.trans a b
        { exact ihab }
        { exact ihbc } }
    { intro h
      apply Star.base
      exact h }

@[simp] theorem Star_Star_Eq_Star {α : Type}
      (R : α → α → Prop) :
    Star (Star R) = Star R :=
  by
    apply funext
    intro a
    apply funext
    intro b
    apply propext
    apply Star_Star_Iff_Star

#check funext
#check propext


/- ## 消解

给定归纳谓词`P`，其引入规则通常形如`∀…, ⋯ → P …`，可用于证明形如`⊢ P …`的目标。

消解则相反：它从形如`P …`的定理或假设中提取信息。消解有多种形式：模式匹配、`cases`和`induction`策略，以及自定义消解规则(如`And.left`)。

* `cases`类似于`induction`但没有归纳假设。

* 也可使用`match`。

现在我们终于能理解`cases h`(当`h : l = r`)和`cases Classical.em h`的工作原理了。 -/

#print Eq

theorem cases_Eq_example {α : Type} (l r : α) (h : l = r)
      (P : α → α → Prop) :
    P l r :=
  by
    cases h
    sorry

#check Classical.em
#print Or

theorem cases_Classical_em_example {α : Type} (a : α)
      (P Q : α → Prop) :
    Q a :=
  by
    have hor : P a ∨ ¬ P a :=
      Classical.em (P a)
    cases hor with
    | inl hl => sorry
    | inr hr => sorry

/- 通常重写形如`P (c …)`的具体项很方便，其中`c`通常是构造子。我们可以陈述并证明一个__反演规则__来支持这种消解推理。

典型的反演规则：

    `∀x y, P (c x y) → (∃…, ⋯ ∧ ⋯) ∨ ⋯ ∨ (∃…, ⋯ ∧ ⋯)`

将引入和消结合并为一个定理很有用，可用于重写目标的假设和结论：

    `∀x y, P (c x y) ↔ (∃…, ⋯ ∧ ⋯) ∨ ⋯ ∨ (∃…, ⋯ ∧ ⋯)` -/

theorem Even_Iff (n : ℕ) :
    Even n ↔ n = 0 ∨ (∃m : ℕ, n = m + 2 ∧ Even m) :=
  by
    apply Iff.intro
    { intro hn
      cases hn with
      | zero         => simp
      | add_two k hk =>
        apply Or.inr
        apply Exists.intro k
        simp [hk] }
    { intro hor
      cases hor with
      | inl heq => simp [heq, Even.zero]
      | inr hex =>
        cases hex with
        | intro k hand =>
          cases hand with
          | intro heq hk =>
            simp [heq, Even.add_two _ hk] }

theorem Even_Iff_struct (n : ℕ) :
    Even n ↔ n = 0 ∨ (∃m : ℕ, n = m + 2 ∧ Even m) :=
  Iff.intro
    (assume hn : Even n
     match n, hn with
     | _, Even.zero         =>
       show 0 = 0 ∨ _ from
         by simp
     | _, Even.add_two k hk =>
       show _ ∨ (∃m, k + 2 = m + 2 ∧ Even m) from
         Or.inr (Exists.intro k (by simp [*])))
    (assume hor : n = 0 ∨ (∃m, n = m + 2 ∧ Even m)
     match hor with
     | Or.inl heq =>
       show Even n from
         by simp [heq, Even.zero]
     | Or.inr hex =>
       match hex with
       | Exists.intro m hand =>
         match hand with
         | And.intro heq hm =>
           show Even n from
             by simp [heq, Even.add_two _ hm])


/- ## 更多示例

### 有序列表 -/

inductive Sorted : List ℕ → Prop where
  | nil : Sorted []
  | single (x : ℕ) : Sorted [x]
  | two_or_more (x y : ℕ) {zs : List ℕ} (hle : x ≤ y)
      (hsorted : Sorted (y :: zs)) :
    Sorted (x :: y :: zs)

theorem Sorted_nil :
    Sorted [] :=
  Sorted.nil

theorem Sorted_2 :
    Sorted [2] :=
  Sorted.single _

theorem Sorted_3_5 :
    Sorted [3, 5] :=
  by
    apply Sorted.two_or_more
    { simp }
    { exact Sorted.single _ }

theorem Sorted_3_5_raw :
    Sorted [3, 5] :=
  Sorted.two_or_more _ _ (by simp) (Sorted.single _)

theorem sorted_7_9_9_11 :
    Sorted [7, 9, 9, 11] :=
  Sorted.two_or_more _ _ (by simp)
    (Sorted.two_or_more _ _ (by simp)
       (Sorted.two_or_more _ _ (by simp)
          (Sorted.single _)))

theorem Not_Sorted_17_13 :
    ¬ Sorted [17, 13] :=
  by
    intro h
    cases h with
    | two_or_more _ _ hlet hsorted => simp at hlet


/- ### 回文 -/

inductive Palindrome {α : Type} : List α → Prop where
  | nil : Palindrome []
  | single (x : α) : Palindrome [x]
  | sandwich (x : α) (xs : List α) (hxs : Palindrome xs) :
    Palindrome ([x] ++ xs ++ [x])

/-
-- 失败
def palindromeRec {α : Type} : List α → Bool
  | []                 => true
  | [_]                => true
  | ([x] ++ xs ++ [x]) => palindromeRec xs
  | _                  => false
-/

theorem Palindrome_aa {α : Type} (a : α) :
    Palindrome [a, a] :=
  Palindrome.sandwich a _ Palindrome.nil

theorem Palindrome_aba {α : Type} (a b : α) :
    Palindrome [a, b, a] :=
  Palindrome.sandwich a _ (Palindrome.single b)

theorem Palindrome_reverse {α : Type} (xs : List α)
      (hxs : Palindrome xs) :
    Palindrome (reverse xs) :=
  by
    induction hxs with
    | nil                  => exact Palindrome.nil
    | single x             => exact Palindrome.single x
    | sandwich x xs hxs ih =>
      { simp [reverse, reverse_append]
        exact Palindrome.sandwich _ _ ih }


/- ### 满二叉树 -/

#check Tree

inductive IsFull {α : Type} : Tree α → Prop where
  | nil : IsFull Tree.nil
  | node (a : α) (l r : Tree α)
      (hl : IsFull l) (hr : IsFull r)
      (hiff : l = Tree.nil ↔ r = Tree.nil) :
    IsFull (Tree.node a l r)

theorem IsFull_singleton {α : Type} (a : α) :
    IsFull (Tree.node a Tree.nil Tree.nil) :=
  by
    apply IsFull.node
    { exact IsFull.nil }
    { exact IsFull.nil }
    { rfl }

theorem IsFull_mirror {α : Type} (t : Tree α)
      (ht : IsFull t) :
    IsFull (mirror t) :=
  by
    induction ht with
    | nil                             => exact IsFull.nil
    | node a l r hl hr hiff ih_l ih_r =>
      { rw [mirror]
        apply IsFull.node
        { exact ih_r }
        { exact ih_l }
        { simp [mirror_Eq_nil_Iff, *] } }

theorem IsFull_mirror_struct_induct {α : Type} (t : Tree α) :
    IsFull t → IsFull (mirror t) :=
  by
    induction t with
    | nil                  =>
      { intro ht
        exact ht }
    | node a l r ih_l ih_r =>
      { intro ht
        cases ht with
        | node _ _ _ hl hr hiff =>
          { rw [mirror]
            apply IsFull.node
            { exact ih_r hr }
            { apply ih_l hl }
            { simp [mirror_Eq_nil_Iff, *] } } }


/- ### 一阶项 -/

inductive Term (α β : Type) : Type where
  | var : β → Term α β
  | fn  : α → List (Term α β) → Term α β

inductive WellFormed {α β : Type} (arity : α → ℕ) :
  Term α β → Prop where
  | var (x : β) : WellFormed arity (Term.var x)
  | fn (f : α) (ts : List (Term α β))
      (hargs : ∀t ∈ ts, WellFormed arity t)
      (hlen : length ts = arity f) :
    WellFormed arity (Term.fn f ts)

inductive VariableFree {α β : Type} : Term α β → Prop where
  | fn (f : α) (ts : List (Term α β))
      (hargs : ∀t ∈ ts, VariableFree t) :
    VariableFree (Term.fn f ts)

end LoVe

