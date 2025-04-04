/- 版权 © 2018–2025 Anne Baanen, Alexander Bentkamp, Jasmin Blanchette,
Xavier Généreux, Johannes Hölzl, 和 Jannis Limperg。参见 `LICENSE.txt`。 -/

import LoVe.LoVe12_LogicalFoundationsOfMathematics_Demo


/- # LoVe 练习12：数学的逻辑基础

将占位符（例如`:= sorry`）替换为你的解答。 -/


set_option autoImplicit false
set_option tactic.hygienic false

namespace LoVe


/- ## 问题1：作为子类型的向量

回顾演示中向量的定义： -/

#check Vector

/- 以下函数逐元素相加两个整数列表。如果一个列表比另一个长，则较长列表的尾部将被忽略。 -/

def List.add : List ℤ → List ℤ → List ℤ
  | [],      []      => []
  | x :: xs, y :: ys => (x + y) :: List.add xs ys
  | [],      y :: ys => []
  | x :: xs, []      => []

/- 1.1. 证明如果两个列表长度相同，结果列表也具有相同的长度。 -/

theorem List.length_add :
    ∀xs ys, List.length xs = List.length ys →
      List.length (List.add xs ys) = List.length xs
  | [], [] =>
    sorry
  | x :: xs, y :: ys =>
    sorry
  | [], y :: ys =>
    sorry
  | x :: xs, [] =>
    sorry

/- 1.2. 使用`List.add`和`List.length_add`定义向量的逐元素加法。 -/

def Vector.add {n : ℕ} : Vector ℤ n → Vector ℤ n → Vector ℤ n :=
  sorry

/- 1.3. 证明`List.add`和`Vector.add`满足交换律。 -/

theorem List.add.comm :
    ∀xs ys, List.add xs ys = List.add ys xs :=
  sorry

theorem Vector.add.comm {n : ℕ} (u v : Vector ℤ n) :
    Vector.add u v = Vector.add v u :=
  sorry


/- ## 问题2：作为商类型的整数

回顾讲座中整数的构造（不要与Lean预定义类型`Int`（即`ℤ`）混淆）： -/

#check Int.Setoid
#check Int.Setoid_Iff
#check Int

/- 2.1. 定义这些整数的取反运算。注意如果`(p, n)`表示一个整数，那么`(n, p)`表示其相反数。 -/

def Int.neg : Int → Int :=
  sorry

/- 2.2. 证明以下关于取反的定理。 -/

theorem Int.neg_eq (p n : ℕ) :
    Int.neg ⟦(p, n)⟧ = ⟦(n, p)⟧ :=
  sorry

theorem int.neg_neg (a : Int) :
    Int.neg (Int.neg a) = a :=
  sorry

end LoVe

