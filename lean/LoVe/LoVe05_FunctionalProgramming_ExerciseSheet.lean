/- 版权 © 2018–2025 Anne Baanen, Alexander Bentkamp, Jasmin Blanchette,
Xavier Généreux, Johannes Hölzl 和 Jannis Limperg。参见 `LICENSE.txt`。 -/

import LoVe.LoVe04_ForwardProofs_Demo


/- # LoVe 练习5：函数式编程

将占位符（例如 `:= sorry`）替换为你的解答。 -/


set_option autoImplicit false
set_option tactic.hygienic false

namespace LoVe


/- ## 问题1：列表的反转

我们定义一个基于累加器的`reverse`变体。第一个参数`as`作为累加器。这个定义是__尾递归的__，意味着编译器和解释器可以轻松优化掉递归，从而生成更高效的代码。 -/

def reverseAccu {α : Type} : List α → List α → List α
  | as, []      => as
  | as, x :: xs => reverseAccu (x :: as) xs

/- 1.1. 我们的意图是`reverseAccu [] xs`应该等于`reverse xs`。但如果开始归纳，我们很快发现归纳假设不够强。首先证明以下推广（使用`induction`策略或模式匹配）： -/

theorem reverseAccu_Eq_reverse_append {α : Type} :
    ∀as xs : List α, reverseAccu as xs = reverse xs ++ as :=
  -- 我们同时对 xs 做归纳，并把累加器 as 泛化进去
  by
    intro as xs
    induction xs generalizing as with
    | nil => rfl
    | cons x xs ih =>
      simp [reverseAccu, ih (x :: as), reverse]



/- 1.2. 推导出所需的等式。 -/

theorem reverseAccu_eq_reverse {α : Type} (xs : List α) :
    reverseAccu [] xs = reverse xs :=
    by
      simp [reverseAccu_Eq_reverse_append]

/- 1.3. 证明以下性质。

提示：可以一行无归纳证明。 -/

theorem reverseAccu_reverseAccu {α : Type} (xs : List α) :
    reverseAccu [] (reverseAccu [] xs) = xs :=
  by
    simp [reverseAccu_eq_reverse, reverse_reverse]

/- 1.4. 通过结构归纳法证明以下定理，作为"纸面"证明。这是深入理解结构归纳法如何工作的好练习（也是期末考试的好练习）。

    theorem reverseAccu_Eq_reverse_append {α : Type} :
      ∀as xs : list α, reverseAccu as xs = reverse xs ++ as

纸面证明指南：

我们期望详细、严谨的数学证明。你可以使用标准数学符号或Lean结构化命令（例如`assume`、`have`、`show`、`calc`）。也可以使用策略证明（例如`intro`、`apply`），但请注明中间目标，以便我们理解推理链条。

主要证明步骤，包括归纳法的应用和归纳假设的调用，必须明确说明。对于归纳证明的每个情况，必须列出假设的归纳假设（如果有）和要证明的目标。对应于`rfl`或`simp`的小步骤如果认为对人是显而易见的，则无需解释，但应说明依赖的关键定理。使用函数定义时应明确说明。 -/

-- 在此处输入你的纸面证明


/- ## 问题2：Drop和Take

`drop`函数移除列表前`n`个元素。 -/

def drop {α : Type} : ℕ → List α → List α
  | 0,     xs      => xs
  | _ + 1, []      => []
  | m + 1, _ :: xs => drop m xs

/- 2.1. 定义`take`函数，返回列表前`n`个元素组成的列表。

为了避免证明中的意外情况，建议遵循与上述`drop`相同的递归模式。 -/

def take {α : Type} : ℕ → List α → List α
  | 0,     _      => []
  | _ + 1, []      => []
  | m + 1, x :: xs => x :: take m xs

#eval take 0 [3, 7, 11]   -- 期望: []
#eval take 1 [3, 7, 11]   -- 期望: [3]
#eval take 2 [3, 7, 11]   -- 期望: [3, 7]
#eval take 3 [3, 7, 11]   -- 期望: [3, 7, 11]
#eval take 4 [3, 7, 11]   -- 期望: [3, 7, 11]

#eval take 2 ["a", "b", "c"]   -- 期望: ["a", "b"]

/- 2.2. 使用`induction`或模式匹配证明以下定理。注意它们通过`@[simp]`属性注册为简化规则。 -/

@[simp] theorem drop_nil {α : Type} :
    ∀n : ℕ, drop n ([] : List α) = [] :=
  assume n : ℕ
  match n with
    | Nat.zero => by rfl
    | Nat.succ x => by rfl

@[simp] theorem take_nil {α : Type} :
    ∀n : ℕ, take n ([] : List α) = [] :=
  assume n : ℕ
  match n with
    | Nat.zero => by rfl
    | Nat.succ x => by rfl

/- 2.3. 遵循`drop`和`take`的递归模式证明以下定理。换句话说，每个定理应有三种情况，第三种情况需要调用归纳假设。

提示：注意`drop_drop`定理中有三个变量（但`drop`只有两个参数）。对于第三种情况，`← add_assoc`可能有用。 -/

theorem drop_drop {α : Type} :
    ∀(m n : ℕ) (xs : List α), drop n (drop m xs) = drop (n + m) xs
  | 0,     n, xs      => by rfl
  | _ + 1, n, []      => by simp [drop]
  | m + 1, n, x :: xs =>
    by
      simp [drop]
      apply drop_drop

theorem take_take {α : Type} :
    ∀(m : ℕ) (xs : List α), take m (take m xs) = take m xs
  |     0, xs      => by rfl
  | _ + 1, []      => by simp [take]
  | m + 1, x :: xs =>
    by
      simp [take]
      apply take_take

theorem take_drop {α : Type} :
    ∀(n : ℕ) (xs : List α), take n xs ++ drop n xs = xs
  |     0, xs      => by rfl
  | _ + 1, []      => by simp [take, drop]
  | n + 1, x :: xs =>
    by
      simp [take, drop]
      apply take_drop


/- ## 问题3：项的类型的类型

3.1. 定义一个归纳类型，对应于无类型λ演算的项，由以下语法给出：

    Term  ::=  `var` String        -- 变量（例如`x`）
            |  `lam` String Term   -- λ表达式（例如`λx. t`）
            |  `app` Term Term     -- 应用（例如`t u`） -/

-- 在此输入你的定义

inductive Term : Type where
  | var : String → Term
  | lam : String → Term → Term
  | app : Term → Term → Term

/- 3.2 (**可选**). 将类型`Term`的文本表示注册为`Repr`类型类的实例。确保提供足够的括号以保证输出无歧义。 -/

def Term.repr : Term → String
| var x => x
| lam x t => "(λ" ++ x ++ ". " ++ (Term.repr t)++ ")"
| app t u => "(" ++ (Term.repr t) ++ " " ++ (Term.repr u) ++ ")"

instance Term.Repr : Repr Term :=
  { reprPrec := fun t _ ↦ Term.repr t }

/- 3.3 (**可选**). 测试你的文本表示。以下命令应打印类似`(λx. ((y x) x))`的内容。 -/

#eval (Term.lam "x" (Term.app (Term.app (Term.var "y") (Term.var "x"))
    (Term.var "x")))

end LoVe
