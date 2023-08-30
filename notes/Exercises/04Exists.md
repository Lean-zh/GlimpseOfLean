```lean
import GlimpseOfLean.Library.Basic

open Function
```

## 逻辑连接词

在这个文件中，我们学习如何处理合取（“逻辑与”）运算符和存在量词。

在 Lean 中，两个命题 P 和 Q 的合取用 P ∧ Q 表示，读作“P 和 Q”。

我们可以像使用 ↔ 一样使用合取：
* 如果 h : P ∧ Q，则 h.1 : P 且 h.2 : Q。
* 要证明 P ∧ Q，使用 constructor 策略。

此外，我们可以分解合取和等价关系。
* 如果 h : P ∧ Q，tactic `rcases h with ⟨hP, hQ⟩`
  会给出两个新的假设 hP : P 和 hQ : Q。
* 如果 h : P ↔ Q，tactic `rcases h with ⟨hPQ, hQP⟩`
  会给出两个新的假设 hPQ : P → Q 和 hQP : Q → P。

```lean
example (p q r s : Prop) (h : p → r) (h' : q → s) : p ∧ q → r ∧ s := by {
  intro hpq
  rcases hpq with ⟨hp, hq⟩
  constructor
  · exact h hp
  · exact h' hq
}
```

也可以使用聚集引号 `⟨`/`⟩` 在不使用 constructor 策略的情况下证明合取，因此上述证明可以重写为。

```lean
example (p q r s : Prop) (h : p → r) (h' : q → s) : p ∧ q → r ∧ s := by {
  intro hpq
  exact ⟨h hpq.1, h' hpq.2⟩
}
```

下一个练习中可以选择自己的风格。

```lean
example (p q r : Prop) : (p → (q → r)) ↔ p ∧ q → r := by {
  sorry
}
```

当然，Lean 不需要任何帮助来证明这种逻辑重言式。
这是 `tauto` 策略的任务，它可以证明命题逻辑中的真命题。

```lean
example (p q r : Prop) : (p → (q → r)) ↔ p ∧ q → r := by {
  tauto
}
```

# 存在量词

为了证明 `∃ x, P x`，我们使用 `use x₀` 策略来给出一些 `x₀`，然后
# 存在量词

为了证明 `∃ x, P x`，我们使用 `use x₀` 策略来给出一些 x₀，然后证明 `P x₀`。这个 x₀ 可以是来自本地上下文的对象，也可以是一个更复杂的表达式。在下面的例子中，用 `use` 之后要检查的性质在定义上是成立的，所以证明已经完成。

```lean
example : ∃ n : ℕ, 8 = 2*n := by {
  use 4
}
```

为了使用 `h : ∃ x, P x`，我们使用 `rcases` 策略来固定一个适用的 x₀。

同样，`h` 可以直接来自本地上下文，也可以是一个更复杂的表达式。

```lean
example (n : ℕ) (h : ∃ k : ℕ, n = k + 1) : n > 0 := by {
  -- 让我们固定一个使得 n = k₀ + 1 的 k₀。
  rcases h with ⟨k₀, hk₀⟩
  -- 现在只需要证明 k₀ + 1 > 0。
  rw [hk₀]
  -- 这个引理可以证明。
  exact Nat.succ_pos k₀
}
```

下面的练习使用 ℤ 中的整除性质（注意 ∣ 符号不是 ASCII）。

根据定义，`a ∣ b ↔ ∃ k, b = a*k`。所以你可以使用 `use` 策略来证明 `a ∣ b`。

```lean
example (a b c : ℤ) (h₁ : a ∣ b) (h₂ : b ∣ c) : a ∣ c := by {
  sorry
}
```

现在我们可以开始组合量词，使用定义

  `Surjective (f : X → Y) := ∀ y, ∃ x, f x = y`

```lean
example (f g : ℝ → ℝ) (h : Surjective (g ∘ f)) : Surjective g := by {
  sorry
}
```

这是关于 `∃` 和 `∧` 的文件的结尾。你已经学习了以下策略：
* `rcases`
* `tauto`
* `use`

这是 `Basics` 文件夹的结尾。我们有意省略了逻辑或运算符和关于否定的所有内容，以便让你尽快进入实际的数学内容。现在你可以从 `Topics` 中选择一个文件了。

在 `03Forall` 的末尾可以找到各个选择的描述。
