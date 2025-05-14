/- 版权所有 © 2018–2025 Anne Baanen, Alexander Bentkamp, Jasmin Blanchette,
Xavier Généreux, Johannes Hölzl, 以及 Jannis Limperg。参见 `LICENSE.txt`。 -/

import LoVe.LoVe02_ProgramsAndTheorems_Demo


/- # LoVe 作业2（10分）：程序与定理

将占位符（例如 `:= sorry`）替换为你的解答。 -/


set_option autoImplicit false
set_option tactic.hygienic false

namespace LoVe


/- ## 问题1（4分）：尾部追加

1.1（3分）。定义函数 `snoc`，该函数将一个元素追加到列表的末尾。你的函数应通过递归定义，且不使用 `++`（`List.append`）。 -/

def snoc {α : Type} : List α → α → List α
  | [],      y => [ y ]
  | x :: xs, y => x :: snoc xs y

/- 1.2（1分）。通过几个示例测试你的 `snoc` 定义，确保其正常工作。 -/

#eval snoc [1] 2
#eval snoc [] 0
#eval snoc [3, 2, 1] 0
-- 在此处调用 `#eval` 或 `#reduce`


/- ## 问题2（6分）：求和

2.1（3分）。定义一个 `sum` 函数，计算列表中所有数字的和。 -/

def sum : List ℕ → ℕ
  | [] => 0
  | x :: xs => x + sum xs

#eval sum [1, 12, 3]   -- 预期结果：16

/- 2.2（3分）。将以下 `sum` 函数的性质陈述为定理（无需证明）。大致如下：

     sum (snoc ms n) = n + sum ms
     sum (ms ++ ns) = sum ms + sum ns
     sum (reverse ns) = sum ns

尝试为你的定理赋予有意义的名称。使用 `sorry` 作为证明。 -/

-- 在此处输入你的定理陈述

theorem sum_snoc (n: ℕ) (ms: List ℕ):
  sum (snoc ms n) = n + sum ms := sorry

theorem sum_concat (ms ns: List ℕ):
  sum (ms ++ ns) = sum ms + sum ns := sorry

theorem sum_reverse (ns: List ℕ):
  sum (reverse ns) = sum ns := sorry

end LoVe
