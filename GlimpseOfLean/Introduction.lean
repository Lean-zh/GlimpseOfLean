

import GlimpseOfLean.Library.Basic

namespace Introduction

/- # 本教程简介

如果你的屏幕较小，可以按下
`alt-Z`（或`option-Z`）来启用自动换行。

欢迎来到本教程，本教程旨在让你在几个小时内对 Lean 有个初步的了解。

首先，让我们看看一个 Lean 证明是什么样子的，尽管不必理解任何语法细节。在这个文件中，你无需输入任何内容。

如果一切正常，你现在在这篇文章的右边会看到一个标题为
"Lean Infoview" 的面板，上面显示着像 "No info found." 这样的信息。
这个面板在证明的过程中会显示有趣的内容。

首先让我们来复习下两个微积分的定义。
-/

/- 一个实数序列 `u` 收敛于 `l` 的条件是当 `∀ ε > 0, ∃ N, ∀ n ≥ N, |u_n - l| ≤ ε`。这个条件将被表示为 `seq_limit u l`。
-/

def seq_limit (u : ℕ → ℝ) (l : ℝ) : Prop :=
∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - l| ≤ ε

/- 在上述定义中，请注意序列 `u` 的第 `n` 项被简单地记作 `u n`。

类似地，在下一个定义中，`f x` 是我们在纸上写作 `f(x)` 的形式。 还要注意，蕴含关系由一个箭头表示（我们稍后会解释原因）。
-/

/- 一个函数 `f : ℝ → ℝ` 在 `x₀` 处连续，如果满足以下条件：
`∀ ε > 0, ∃ δ > 0, ∀ x, |x - x₀| ≤ δ ⇒ |f(x) - f(x₀)| ≤ ε`。
这个条件将被说明为 `continuous_at f x₀`。
-/

def continuous_at (f : ℝ → ℝ) (x₀ : ℝ) : Prop :=
∀ ε > 0, ∃ δ > 0, ∀ x, |x - x₀| ≤ δ → |f x - f x₀| ≤ ε

/- 现在我们要证明：如果函数 `f` 在 `x₀` 处连续，那么它在 `x₀` 处就是序列连续的：对于任何收敛于 `x₀` 的序列 `u`，序列 `f ∘ u` 收敛于 `f x₀`。
-/

example (f : ℝ → ℝ) (u : ℕ → ℝ) (x₀ : ℝ) (hu : seq_limit u x₀) (hf : continuous_at f x₀) :
  seq_limit (f ∘ u) (f x₀) := by { -- This `by` keyword marks the beginning of the proof
  -- Put your text cursor here and watch the Lean InfoView panel to the right.
  -- Then move your cursor from line to line in the proof while monitoring the Infoview.

  -- Our goal is to prove that, for any positive `ε`, there exists a natural
  -- number `N` such that, for any natural number `n` at least `N`,
  --  `|f(u_n) - f(x₀)|` is at most `ε`.
  unfold seq_limit
  -- Fix a positive number `ε`.
  intros ε hε
  -- By assumption on `f` applied to this positive `ε`, we get a positive `δ`
  -- such that, for all real number `x`, if `|x - x₀| ≤ δ` then `|f(x) - f(x₀)| ≤ ε` (1).
  obtain ⟨δ, δ_pos, Hf⟩ : ∃ δ > 0, ∀ x, |x - x₀| ≤ δ → |f x - f x₀| ≤ ε := hf ε hε
  -- The assumption on `u` applied to this `δ` gives a natural number `N` such that
  -- for every natural number `n`, if `n ≥ N` then `|u_n - x₀| ≤ δ`   (2).
  obtain ⟨N, Hu⟩ : ∃ N, ∀ n ≥ N, |u n - x₀| ≤ δ := hu δ δ_pos
  -- Let's prove `N` is suitable.
  use N
  -- Fix `n` which is at least `N`. Let's prove `|f(u_n) - f(x₀)| ≤ ε`.
  intros n hn
  -- Thanks to (1) applied to `u_n`, it suffices to prove that `|u_n - x₀| ≤ δ`.
  apply Hf
  -- This follows from property (2) and our assumption on `n`.
  exact Hu n hn
  -- This finishes the proof!
  }

/- 现在这个证明已经结束，你可以使用面板左侧的文件浏览器打开 `练习 > 01重写.lean`文件。
-/

/- 
-/