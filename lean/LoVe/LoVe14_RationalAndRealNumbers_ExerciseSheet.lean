/- 版权所有 © 2018–2025 Anne Baanen, Alexander Bentkamp, Jasmin Blanchette,
Xavier Généreux, Johannes Hölzl, 以及 Jannis Limperg。参见 `LICENSE.txt`。 -/

import LoVe.LoVe06_InductivePredicates_Demo
import LoVe.LoVe14_RationalAndRealNumbers_Demo


/- # LoVe 练习14：有理数与实数

将占位符（例如`:= sorry`）替换为你的解答。 -/


set_option autoImplicit false
set_option tactic.hygienic false

namespace LoVe


/- ## 问题1：有理数

1.1. 证明以下定理。

提示：

* 首先对`a`和`b`进行情况分析。

* 当目标开始变得复杂时，使用`simp at *`来简化它。 -/

theorem Fraction.ext (a b : Fraction) (hnum : Fraction.num a = Fraction.num b)
      (hdenom : Fraction.denom a = Fraction.denom b) :
    a = b :=
  sorry

/- 1.2. 扩展讲座中的`Fraction.Mul`实例，将`Fraction`声明为`Semigroup`的实例。

提示：使用上述定理`Fraction.ext`，可能还需要`Fraction.mul_num`和`Fraction.mul_denom`。 -/

#check Fraction.ext
#check Fraction.mul_num
#check Fraction.mul_denom

instance Fraction.Semigroup : Semigroup Fraction :=
  { Fraction.Mul with
    mul_assoc :=
      sorry
  }

/- 1.3. 扩展讲座中的`Rat.Mul`实例，将`Rat`声明为`Semigroup`的实例。 -/

instance Rat.Semigroup : Semigroup Rat :=
  { Rat.Mul with
    mul_assoc :=
      sorry
  }

end LoVe

