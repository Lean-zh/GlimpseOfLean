

import GlimpseOfLean.Library.Basic

open Function

/- ## 合取

在此文件中，我们将学习如何处理合取（"逻辑与"）运算符和存在量词。

在 Lean 中，两个陈述 `P` 和 `Q` 的合取表示为 `P ∧ Q`，读作 "P and Q"。

我们可以类似于 `↔` 来使用合取：
* 如果 `h : P ∧ Q` 那么 `h.1 : P` 和 `h.2 : Q`。
* 为了证明 `P ∧ Q`，使用 `constructor` 策略。

此外，我们可以分解合取和等价。
* 如果 `h : P ∧ Q`，策略 `rcases h with ⟨hP, hQ⟩`
  会给出两个新的假设 `hP : P` 和 `hQ : Q`。
* 如果 `h : P ↔ Q`，策略 `rcases h with ⟨hPQ, hQP⟩`
  会给出两个新的假设 `hPQ : P → Q` 和 `hQP : Q → P`。
-/

example (p q r s : Prop) (h : p → r) (h' : q → s) : p ∧ q → r ∧ s := by {
  intro hpq
  rcases hpq with ⟨hp, hq⟩
  constructor
  · exact h hp
  · exact h' hq
}

/- 我们也可以在不使用构造函数策略的情况下证明一个并列关系，通过使用 `⟨`/`⟩` 括号收集两侧内容，所以上述的证明可以被重写为。
-/

example (p q r s : Prop) (h : p → r) (h' : q → s) : p ∧ q → r ∧ s := by {
  intro hpq
  exact ⟨h hpq.1, h' hpq.2⟩
}

/- 你可以在下一个练习中选择你自己的风格。


-/

example (p q r : Prop) : (p → (q → r)) ↔ p ∧ q → r := by {
  sorry
}

/- 当然，Lean 在证明这类逻辑恒等式方面并不需要任何帮助。这是 `tauto` 策略的工作，它能在命题逻辑中证明真实的陈述。
-/

example (p q r : Prop) : (p → (q → r)) ↔ p ∧ q → r := by {
  tauto
}

/- # 存在量词

为了证明 `∃ x, P x` ，我们提供某些 `x₀` ，使用策略 `use x₀` ，
然后证明 `P x₀` 。这个 `x₀` 可以是来自局部环境的对象
或者更复杂的表达式。在下面的例子中， `use` 后要检查的属性按照定义是正确的，所以证明到此结束。
-/

example : ∃ n : ℕ, 8 = 2*n := by {
  use 4
}

/- 为了使用 `h : ∃ x, P x`，我们使用 `rcases` 策略来固定一个有效的 `x₀`。

同样，`h` 可以直接来自本地上下文，也可以是更复杂的表达式。
-/

example (n : ℕ) (h : ∃ k : ℕ, n = k + 1) : n > 0 := by {
  -- Let's fix k₀ such that n = k₀ + 1.
  rcases h with ⟨k₀, hk₀⟩
  -- It now suffices to prove k₀ + 1 > 0.
  rw [hk₀]
  -- and we have a lemma about this
  exact Nat.succ_pos k₀
}

/- 接下来的习题将使用ℤ中的整除（注意 ∣ 符号，它不是 ASCII）。

根据定义，`a ∣ b ↔ ∃ k, b = a*k`，所以你可以使用 `use` 策略来证明 `a ∣ b`。
-/

example (a b c : ℤ) (h₁ : a ∣ b) (h₂ : b ∣ c) : a ∣ c := by {
  sorry
}

/- 我们现在可以开始结合量词，使用定义

  `Surjective (f : X → Y) := ∀ y, ∃ x, f x = y`

这是 "映射的反向" 的定义。意思是对于所有的 `y`，都存在某个 `x`，使得 `f` 函数作用于 `x` 之后得到 `y`。
-/

example (f g : ℝ → ℝ) (h : Surjective (g ∘ f)) : Surjective g := by {
  sorry
}

/- 这是关于 `∃` 和 `∧` 的文件的结尾。你已经学到了以下技巧：
* `rcases`
* `tauto`
* `use`

这是 `基础` 文件夹的结束。我们故意没有包括逻辑或运算符
和所有关于否定的内容，以便你能尽快进入
实际的数学内容。你现在可以从 `主题` 中选择一个文件。

请查看 `03Forall` 底部对可选项的描述。
-/

/- 
-/