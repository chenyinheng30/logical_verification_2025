/- 版权 © 2018–2025 Anne Baanen, Alexander Bentkamp, Jasmin Blanchette,
Xavier Généreux, Johannes Hölzl, 和 Jannis Limperg。参见 `LICENSE.txt`。 -/

import LoVe.LoVelib


/- # LoVe 演示2：程序与定理

我们继续学习Lean的基础知识，重点放在程序和定理上，暂时不进行任何证明。我们将回顾如何定义新类型和函数，以及如何将它们预期的性质表述为定理。 -/


set_option autoImplicit false
set_option tactic.hygienic false

namespace LoVe


/- ## 类型定义

__归纳类型__（也称为__归纳数据类型__、__代数数据类型__或简称__数据类型__）是一种类型，它包含所有可以通过有限次应用其__构造子__构建的值，且仅包含这些值。


### 自然数 -/

namespace MyNat

/- 使用一元表示法定义自然数类型 `Nat`（= `ℕ`）： -/

inductive Nat : Type where
  | zero : Nat
  | succ : Nat → Nat

#check Nat
#check Nat.zero
#check Nat.succ

/- `#print` 输出其参数的定义。 -/

#print Nat

end MyNat

/- 在 `MyNat` 命名空间之外，除非加上 `MyNat` 命名空间限定，否则 `Nat` 指的是Lean核心库中定义的类型。 -/

#print Nat
#print MyNat.Nat


/- ### 算术表达式 -/

inductive AExp : Type where
  | num : ℤ → AExp
  | var : String → AExp
  | add : AExp → AExp → AExp
  | sub : AExp → AExp → AExp
  | mul : AExp → AExp → AExp
  | div : AExp → AExp → AExp


/- ### 列表 -/

namespace MyList

inductive List (α : Type) where
  | nil  : List α
  | cons : α → List α → List α

#check List
#check List.nil
#check List.cons
#print List

end MyList

#print List
#print MyList.List


/- ## 函数定义

定义操作于归纳类型的函数语法非常简洁：我们定义一个单一函数，并使用__模式匹配__来提取构造子的参数。 -/

def fib : ℕ → ℕ
  | 0     => 0
  | 1     => 1
  | n + 2 => fib (n + 1) + fib n

/- 当有多个参数时，用 `,` 分隔模式： -/

def add : ℕ → ℕ → ℕ
  | m, Nat.zero   => m
  | m, Nat.succ n => Nat.succ (add m n)

/- `#eval` 和 `#reduce` 计算并输出项的值。 -/

#eval add 2 7
#reduce add 2 7

def mul : ℕ → ℕ → ℕ
  | _, Nat.zero   => Nat.zero
  | m, Nat.succ n => add m (mul m n)

#eval mul 2 7

#print mul

def power : ℕ → ℕ → ℕ
  | _, Nat.zero   => 1
  | m, Nat.succ n => mul m (power m n)

#eval power 2 5

/- `add`、`mul` 和 `power` 是人为示例。这些操作在Lean中已经作为 `+`、`*` 和 `^` 提供。

如果不需要对某个参数进行模式匹配，可以将其移到 `:` 的左侧并作为命名参数： -/

def powerParam (m : ℕ) : ℕ → ℕ
  | Nat.zero   => 1
  | Nat.succ n => mul m (powerParam m n)

#eval powerParam 2 5

def iter (α : Type) (z : α) (f : α → α) : ℕ → α
  | Nat.zero   => z
  | Nat.succ n => f (iter α z f n)

#check iter

def powerIter (m n : ℕ) : ℕ :=
  iter ℕ 1 (mul m) n

#eval powerIter 2 5

def append (α : Type) : List α → List α → List α
  | List.nil,       ys => ys
  | List.cons x xs, ys => List.cons x (append α xs ys)

/- 因为 `append` 必须适用于任何类型的列表，所以元素的类型作为参数提供。因此，在每次调用时必须提供类型（或者如果Lean能推断类型，可以使用 `_`）。 -/

#check append
#eval append ℕ [3, 1] [4, 1, 5]
#eval append _ [3, 1] [4, 1, 5]

/- 如果类型参数用 `{ }` 而不是 `( )` 包围，则它是隐式的，不需要在每次调用时提供（前提是Lean能推断它）。 -/

def appendImplicit {α : Type} : List α → List α → List α
  | List.nil,       ys => ys
  | List.cons x xs, ys => List.cons x (appendImplicit xs ys)

#eval appendImplicit [3, 1] [4, 1, 5]

/- 在定义名前加上 `@` 可以得到所有隐式参数显式化的对应定义。这在Lean无法确定如何实例化隐式参数的情况下非常有用。 -/

#check @appendImplicit
#eval @appendImplicit ℕ [3, 1] [4, 1, 5]
#eval @appendImplicit _ [3, 1] [4, 1, 5]

/- 别名：

    `[]`          := `List.nil`
    `x :: xs`     := `List.cons x xs`
    `[x₁, …, xN]` := `x₁ :: … :: xN :: []` -/

def appendPretty {α : Type} : List α → List α → List α
  | [],      ys => ys
  | x :: xs, ys => x :: appendPretty xs ys

def reverse {α : Type} : List α → List α
  | []      => []
  | x :: xs => reverse xs ++ [x]

def eval (env : String → ℤ) : AExp → ℤ
  | AExp.num i     => i
  | AExp.var x     => env x
  | AExp.add e₁ e₂ => eval env e₁ + eval env e₂
  | AExp.sub e₁ e₂ => eval env e₁ - eval env e₂
  | AExp.mul e₁ e₂ => eval env e₁ * eval env e₂
  | AExp.div e₁ e₂ => eval env e₁ / eval env e₂

#eval eval (fun x ↦ 7) (AExp.div (AExp.var "y") (AExp.num 0))

/- Lean只接受那些它能证明终止的函数定义。特别是，它接受__结构递归__函数，这些函数每次恰好剥离一个构造子。


## 定理陈述

注意与 `def` 命令的相似性。`theorem` 类似于 `def`，只是结果是一个命题而不是数据或函数。 -/

namespace SorryTheorems

theorem add_comm (m n : ℕ) :
    add m n = add n m :=
  sorry

theorem add_assoc (l m n : ℕ) :
    add (add l m) n = add l (add m n) :=
  sorry

theorem mul_comm (m n : ℕ) :
    mul m n = mul n m :=
  sorry

theorem mul_assoc (l m n : ℕ) :
    mul (mul l m) n = mul l (mul m n) :=
  sorry

theorem mul_add (l m n : ℕ) :
    mul l (add m n) = add (mul l m) (mul l n) :=
  sorry

theorem reverse_reverse {α : Type} (xs : List α) :
    reverse (reverse xs) = xs :=
  sorry

/- 公理类似于定理但没有证明。不透明声明类似于定义但没有主体。 -/

opaque a : ℤ
opaque b : ℤ

axiom a_less_b :
    a < b

end SorryTheorems

end LoVe

