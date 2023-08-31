```lean
import GlimpseOfLean.Library.Basic

```
在这个文件中，我们处理实数序列的极限的基本定义。
mathlib有一个更一般的极限定义，但在这里，
我们想要练习使用前面文件中涉及到的逻辑运算符和关系。

在开始之前，让我们确保 Lean 在证明等式或不等式时不需要太多帮助
这是线性算术策略的工作：`linarith`。

```lean
example (a b : ℝ) (hb : 0 ≤ b) : a ≤ a + b := by linarith
```

让我们使用`linarith`证明一些练习。

```lean
example (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ a + b := by {
  sorry
}

example (a b c d : ℝ) (hab : a ≤ b) (hcd : c ≤ d) : a + c ≤ b + d := by {
  sorry
}
```

一个序列 `u` 是从 `ℕ` 到 `ℝ` 的函数，因此 Lean 表示为
`u : ℕ → ℝ`
我们将使用的定义是:

-- « u 收敛到 l 的定义」
`def seq_limit (u : ℕ → ℝ) (l : ℝ) := ∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - l| ≤ ε`

注意使用 `∀ ε > 0, _` 是 对 `∀ ε, ε > 0 → _ ` 的缩写

特别地，类似 `h : ∀ ε > 0, _` 的语句可以通过
  `specialize h ε₀ hε₀`
其中 `hε₀` 是一个证明 `ε₀ > 0`的证明，来进行ε₀的特化。

还要注意，Lean 在期望某个证明项时，我们可以
使用关键字 `by` 开始一个策略模式的证明。
例如，如果局部上下文包含：

δ : ℝ
δ_pos : δ > 0
h : ∀ ε > 0, _

那么我们可以使用 `specialize h (δ/2) (by linarith)` 将 h
特化为实数 δ/2，其中 `by linarith` 将提供 Lean 期望的 `δ/2 > 0` 的证明。

如果 u 是一个值为 l 的常量函数，则 u 收敛到 l。
提示：`simp` 可以将 `|1 - 1|` 重写为 `0`
```
```lean
example (h : ∀ n, u n = l) : seq_limit u l := by {
  sorry
}
```

处理绝对值时，我们将使用引理：

`abs_sub_comm (x y : ℝ) : |x - y| = |y - x|`

`abs_le {x y : ℝ} : |x| ≤ y ↔ -y ≤ x ∧ x ≤ y`

我们还将使用三角不等式的变体

`abs_add (x y : ℝ) : |x + y| ≤ |x| + |y|`
或者
`abs_sub_le (a c b : ℝ) : |a - b| ≤ |a - c| + |c - b|`
或者带有撇号的版本：
`abs_sub_le' (a c b : ℝ) : |a - b| ≤ |a - c| + |b - c|`

```lean
-- 假设 `l > 0`。那么 `u` 收敛到 `l` 意味着对于充分大的 `n`，有 `u n ≥ l/2`
example (h : seq_limit u l) (hl : l > 0) :
  ∃ N, ∀ n ≥ N, u n ≥ l/2 := by {
  sorry
}
```

处理 max 时，可以使用以下引理

`ge_max_iff (p q r) : r ≥ max p q ↔ r ≥ p ∧ r ≥ q`

`le_max_left p q : p ≤ max p q`

`le_max_right p q : q ≤ max p q`

我们来看一个例子：

```lean
-- 如果 `u` 收敛到 `l`，并且 `v` 收敛到 `l'`，那么 `u+v` 收敛到 `l+l'`
example (hu : seq_limit u l) (hv : seq_limit v l') :
  seq_limit (u + v) (l + l') := by {
  intros ε ε_pos
  rcases hu (ε/2) (by linarith) with ⟨N₁, hN₁⟩
  rcases hv (ε/2) (by linarith) with ⟨N₂, hN₂⟩
  use max N₁ N₂
  intros n hn
  have : n ≥ N₁ := by exact le_of_max_le_left hn
  rw [ge_max_iff] at hn
  rcases hn with ⟨hn₁, hn₂⟩
  have fact₁ : |u n - l| ≤ ε/2
  · exact hN₁ n (by linarith)
  have fact₂ : |v n - l'| ≤ ε/2
  · exact hN₂ n (by linarith)

  calc
    |(u + v) n - (l + l')| = |u n + v n - (l + l')|   := rfl
    _ = |(u n - l) + (v n - l')|                      := by ring
    _ ≤ |u n - l| + |v n - l'|                        := by apply abs_add
    _ ≤ ε                                             := by linarith [fact₁, fact₂]
}
```
```
让我们做一个类似的练习：夹逼定理。

```lean
example (hu : seq_limit u l) (hw : seq_limit w l) (h : ∀ n, u n ≤ v n) (h' : ∀ n, v n ≤ w n) :
    seq_limit v l := by {
  sorry
}
```

在接下来的练习中，我们会用到

`eq_of_abs_sub_le_all (x y : ℝ) : (∀ ε > 0, |x - y| ≤ ε) → x = y`

回顾一下，在这个文件的开头列出了三个三角不等式的变体。

```lean
-- 一个数列最多只有一个极限。你可以在下面的练习中使用该引理。
lemma uniq_limit : seq_limit u l → seq_limit u l' → l = l' := by {
  sorry
}
```

现在让我们在证明之前练习阅读定义。

```lean
def non_decreasing (u : ℕ → ℝ) := ∀ n m, n ≤ m → u n ≤ u m

def is_seq_sup (M : ℝ) (u : ℕ → ℝ) :=
(∀ n, u n ≤ M) ∧ ∀ ε > 0, ∃ n₀, u n₀ ≥ M - ε

example (M : ℝ) (h : is_seq_sup M u) (h' : non_decreasing u) : seq_limit u M := by {
  sorry
}
```

现在让我们来玩一下子数列。

我们将使用的新定义是，当 `φ : ℕ → ℕ` 为（严格）递增时，它是抽取函数。

`def extraction (φ : ℕ → ℕ) := ∀ n m, n < m → φ n < φ m`

在下面的练习中，`φ` 将始终表示从 `ℕ` 到 `ℕ` 的一个函数。

下面的引理可以通过简单的归纳来证明，但在本教程中我们还没有见过归纳法。
如果你完成了自然数游戏，你可以删除下面的证明，然后尝试重建它。

抽取函数大于 id 函数

```lean
lemma id_le_extraction' : extraction φ → ∀ n, n ≤ φ n := by {
  intros hyp n
  induction n with
  | zero =>  exact Nat.zero_le _
  | succ n ih => exact Nat.succ_le_of_lt (by linarith [hyp n (n+1) (by linarith)])
}
```

在这个练习中，我们使用了 `∃ n ≥ N, ...`，这是 `∃ n, n ≥ N ∧ ...` 的缩写形式。

抽取函数对于充分大的输入可以取到任意大的值。

```lean
lemma extraction_ge : extraction φ → ∀ N N', ∃ n ≥ N', φ n ≥ N := by {
  sorry
}
}
```
一个实数 `a` 是数列 `u` 的聚点，如果 `u` 存在一个收敛到 `a` 的子数列。

`def cluster_point (u : ℕ → ℝ) (a : ℝ) := ∃ φ, extraction φ ∧ seq_limit (u ∘ φ) a`

如果 `a` 是 `u` 的聚点，那么对于任意大的输入，存在 `u` 的值与 `a` 接近。

```lean
lemma near_cluster :
  cluster_point u a → ∀ ε > 0, ∀ N, ∃ n ≥ N, |u n - a| ≤ ε := by {
  sorry
}
```

如果 `u` 收敛到 `l`，那么它的子数列也会收敛到 `l`。

```lean
lemma subseq_tendsto_of_tendsto' (h : seq_limit u l) (hφ : extraction φ) :
seq_limit (u ∘ φ) l := by {
  sorry
}
```

如果 `u` 收敛到 `l`，那么它的所有聚点都等于 `l`。

```lean
lemma cluster_limit (hl : seq_limit u l) (ha : cluster_point u a) : a = l := by {
  sorry
}
```

柯西数列

```lean
def CauchySequence (u : ℕ → ℝ) :=
  ∀ ε > 0, ∃ N, ∀ p q, p ≥ N → q ≥ N → |u p - u q| ≤ ε

example : (∃ l, seq_limit u l) → CauchySequence u := by {
  sorry
}
```

在下一个练习中，你可以重用以下引理
near_cluster : cluster_point u a → ∀ ε > 0, ∀ N, ∃ n ≥ N, |u n - a| ≤ ε

```lean
example (hu : CauchySequence u) (hl : cluster_point u l) : seq_limit u l := by
  sorry
}
```
